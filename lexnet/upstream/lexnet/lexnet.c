#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef struct {
    int64_t rows, cols, nskip;
    const double *W, *b, *hi;
    const int64_t *skip;
    int *rowptr, *col;      /* CSR view, built at load */
    double *val;
} Layer;

typedef struct {
    int64_t n_feats, n_fstate, n_fout, n_bstate, n_classes, head_cols, maxw;
    const double *emb, *h0, *head_W, *head_b;
    const int64_t *f_state, *f_out, *b_state;
    Layer *fwd, *bwd;
    int64_t n_fwd, n_bwd;
} Net;

static int use_dense = 0, use_interp = 0;

static const char *ANSI[11] = {
    "", "\x1b[1;35m", "\x1b[36m", "\x1b[1;34m", "", "\x1b[33m",
    "\x1b[32m", "\x1b[32m", "\x1b[2;3;37m", "\x1b[38;5;208m", "\x1b[90m",
};

/* ---- loading ------------------------------------------------------------- */
typedef struct { const unsigned char *p, *end; } Cursor;

static const void *take(Cursor *c, size_t bytes) {
    if (c->p + bytes > c->end) { fprintf(stderr, "weights: truncated\n"); exit(1); }
    const void *r = c->p;
    c->p += bytes;
    return r;
}
static int64_t take_i64(Cursor *c) { return *(const int64_t *)take(c, 8); }

static Layer *load_cell(Cursor *c, int64_t *n, int64_t *maxw) {
    *n = take_i64(c);
    Layer *L = calloc((size_t)*n, sizeof(Layer));
    for (int64_t l = 0; l < *n; l++) {
        Layer *y = &L[l];
        y->rows = take_i64(c); y->cols = take_i64(c); y->nskip = take_i64(c);
        y->W = take(c, (size_t)(y->rows * y->cols) * 8);
        y->b = take(c, (size_t)y->rows * 8);
        y->hi = take(c, (size_t)y->rows * 8);
        y->skip = take(c, (size_t)y->nskip * 8);
        if (y->cols > *maxw) *maxw = y->cols;
        if (y->rows + y->nskip > *maxw) *maxw = y->rows + y->nskip;
        /* CSR */
        int nnz = 0;
        for (int64_t i = 0; i < y->rows * y->cols; i++) nnz += y->W[i] != 0;
        y->rowptr = malloc((size_t)(y->rows + 1) * sizeof(int));
        y->col = malloc((size_t)nnz * sizeof(int));
        y->val = malloc((size_t)nnz * sizeof(double));
        int k = 0;
        for (int64_t r = 0; r < y->rows; r++) {
            y->rowptr[r] = k;
            for (int64_t cc = 0; cc < y->cols; cc++) {
                double w = y->W[r * y->cols + cc];
                if (w != 0) y->col[k] = (int)cc, y->val[k++] = w;
            }
        }
        y->rowptr[y->rows] = k;
    }
    return L;
}

static Net load(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); exit(1); }
    fseek(f, 0, SEEK_END);
    size_t n = (size_t)ftell(f);
    fseek(f, 0, SEEK_SET);
    unsigned char *blob = malloc(n);
    if (fread(blob, 1, n, f) != n) { perror(path); exit(1); }
    fclose(f);
    Cursor c = { blob, blob + n };
    if (memcmp(take(&c, 8), "LEXNET01", 8)) { fprintf(stderr, "%s: not a LEXNET01 weight file\n", path); exit(1); }
    Net net = {0};
    net.n_feats = take_i64(&c); net.n_fstate = take_i64(&c); net.n_fout = take_i64(&c);
    net.n_bstate = take_i64(&c); net.n_classes = take_i64(&c); net.head_cols = take_i64(&c);
    net.emb = take(&c, (size_t)(128 * net.n_feats) * 8);
    net.maxw = net.n_feats + net.n_fstate;
    if (net.n_fout + net.n_bstate > net.maxw) net.maxw = net.n_fout + net.n_bstate;
    net.fwd = load_cell(&c, &net.n_fwd, &net.maxw);
    net.bwd = load_cell(&c, &net.n_bwd, &net.maxw);
    net.f_state = take(&c, (size_t)net.n_fstate * 8);
    net.f_out = take(&c, (size_t)net.n_fout * 8);
    net.b_state = take(&c, (size_t)net.n_bstate * 8);
    net.h0 = take(&c, (size_t)net.n_fstate * 8);
    net.head_W = take(&c, (size_t)(net.n_classes * net.head_cols) * 8);
    net.head_b = take(&c, (size_t)net.n_classes * 8);
    if (c.p != c.end) { fprintf(stderr, "weights: %zu trailing bytes\n", (size_t)(c.end - c.p)); exit(1); }
    return net;
}

/* ---- inference ----------------------------------------------------------- */
/* v: activation vector (in/out). Every layer is new = clip(W v + b, 0, hi)
 * followed by a parameter-free concat of carried units. */
static void run_cell(const Layer *layers, int64_t nl, double *v, double *tmp) {
    for (int64_t l = 0; l < nl; l++) {
        const Layer *L = &layers[l];
        for (int64_t r = 0; r < L->rows; r++) {
            double s = L->b[r];
            if (use_dense) {
                const double *w = L->W + r * L->cols;
                for (int64_t c = 0; c < L->cols; c++) s += w[c] * v[c];
            } else {
                for (int k = L->rowptr[r]; k < L->rowptr[r + 1]; k++) s += L->val[k] * v[L->col[k]];
            }
            tmp[r] = s < 0 ? 0 : (s > L->hi[r] ? L->hi[r] : s);
        }
        for (int64_t k = 0; k < L->nskip; k++) tmp[L->rows + k] = v[L->skip[k]];
        memcpy(v, tmp, (size_t)(L->rows + L->nskip) * sizeof(double));
    }
}

/* ---- compiled mode ------------------------------------------------------- */
#include "lexnet_kernel.h"

/* FNV-1a over the architecture (shapes, ceilings, skips, sparsity, index maps). */
typedef struct { uint64_t h; } Fnv;
static void fnv_bytes(Fnv *f, const void *p, size_t n) {
    for (size_t i = 0; i < n; i++) { f->h ^= ((const unsigned char *)p)[i]; f->h *= 0x100000001B3ULL; }
}
static void fnv_i64(Fnv *f, int64_t x) { fnv_bytes(f, &x, 8); }
static void fnv_mask(Fnv *f, const double *a, int64_t n) {
    for (int64_t i = 0; i < n; i++) { unsigned char m = a[i] != 0; fnv_bytes(f, &m, 1); }
}
static uint64_t struct_hash(const Net *net) {
    Fnv f = { 0xCBF29CE484222325ULL };
    fnv_i64(&f, net->n_feats); fnv_i64(&f, net->n_fstate); fnv_i64(&f, net->n_fout);
    fnv_i64(&f, net->n_bstate); fnv_i64(&f, net->n_classes); fnv_i64(&f, net->head_cols);
    const Layer *cells[2] = { net->fwd, net->bwd };
    int64_t counts[2] = { net->n_fwd, net->n_bwd };
    for (int c = 0; c < 2; c++) {
        fnv_i64(&f, counts[c]);
        for (int64_t l = 0; l < counts[c]; l++) {
            const Layer *L = &cells[c][l];
            fnv_i64(&f, L->rows); fnv_i64(&f, L->cols); fnv_i64(&f, L->nskip);
            fnv_bytes(&f, L->hi, (size_t)L->rows * 8);
            for (int64_t k = 0; k < L->nskip; k++) fnv_i64(&f, L->skip[k]);
            fnv_mask(&f, L->W, L->rows * L->cols);
        }
    }
    for (int64_t i = 0; i < net->n_fstate; i++) fnv_i64(&f, net->f_state[i]);
    for (int64_t i = 0; i < net->n_fout; i++) fnv_i64(&f, net->f_out[i]);
    for (int64_t i = 0; i < net->n_bstate; i++) fnv_i64(&f, net->b_state[i]);
    fnv_mask(&f, net->head_W, net->n_classes * net->head_cols);
    return f.h;
}

/* Pull the coefficients the kernel references out of the loaded layers. */
static void gather(const Net *net, double *kc, double *kb) {
    for (int i = 0; i < K_N_COEF; i++) {
        int cell = K_COEF[i][0], l = K_COEF[i][1], r = K_COEF[i][2], c = K_COEF[i][3];
        if (cell == 2) kc[i] = net->head_W[r * net->head_cols + c];
        else { const Layer *L = &(cell ? net->bwd : net->fwd)[l]; kc[i] = L->W[r * L->cols + c]; }
    }
    for (int i = 0; i < K_N_BIAS; i++) {
        int cell = K_BIAS[i][0], l = K_BIAS[i][1], r = K_BIAS[i][2];
        kb[i] = cell == 2 ? net->head_b[r] : (cell ? net->bwd : net->fwd)[l].b[r];
    }
}

static void classify_compiled(const Net *net, const double *kc, const double *kb,
                              const unsigned char *src, size_t n, unsigned char *cls, uint16_t *bits) {
    FState a, b, *p = &a, *s = &b, *t;
    k_init_state(p, net->h0);
    for (size_t i = 0; i < n; i++) {
        bits[i] = k_fwd_step(kc, kb, net->emb + (src[i] < 128 ? src[i] : 127) * K_N_FEATS, p, s);
        t = p; p = s; s = t;
    }
    BState ra = {0}, rb, *r = &ra, *q = &rb, *u;
    for (size_t i = n; i-- > 0;) {
        cls[i] = (unsigned char)k_bwd_step(kc, kb, bits[i], r, q);
        u = r; r = q; q = u;
    }
}

static void classify(const Net *net, const unsigned char *src, size_t n, unsigned char *cls, double *feats) {
    double *v = malloc((size_t)net->maxw * 8), *tmp = malloc((size_t)net->maxw * 8);
    double *h = malloc((size_t)net->n_fstate * 8), *r = calloc((size_t)net->n_bstate, 8);
    memcpy(h, net->h0, (size_t)net->n_fstate * 8);
    for (size_t t = 0; t < n; t++) {
        unsigned c = src[t] < 128 ? src[t] : 127;
        memcpy(v, net->emb + c * net->n_feats, (size_t)net->n_feats * 8);
        memcpy(v + net->n_feats, h, (size_t)net->n_fstate * 8);
        run_cell(net->fwd, net->n_fwd, v, tmp);
        for (int64_t i = 0; i < net->n_fstate; i++) h[i] = v[net->f_state[i]];
        for (int64_t i = 0; i < net->n_fout; i++) feats[t * net->n_fout + i] = v[net->f_out[i]];
    }
    for (size_t t = n; t-- > 0;) {
        memcpy(v, feats + t * net->n_fout, (size_t)net->n_fout * 8);
        memcpy(v + net->n_fout, r, (size_t)net->n_bstate * 8);
        run_cell(net->bwd, net->n_bwd, v, tmp);
        for (int64_t i = 0; i < net->n_bstate; i++) r[i] = v[net->b_state[i]];
        int best = 0;
        double bestv = -1e300;
        for (int64_t k = 0; k < net->n_classes; k++) {
            double s = net->head_b[k];
            for (int64_t c = 0; c < net->head_cols; c++) s += net->head_W[k * net->head_cols + c] * v[c];
            if (s > bestv) bestv = s, best = (int)k;
        }
        cls[t] = (unsigned char)best;
    }
    free(v); free(tmp); free(h); free(r);
}

/* ---- cli ----------------------------------------------------------------- */
static char *default_weights(const char *argv0) {
    const char *slash = strrchr(argv0, '/');
    size_t dir = slash ? (size_t)(slash - argv0 + 1) : 0;
    char *p = malloc(dir + 32);
    memcpy(p, argv0, dir);
    strcpy(p + dir, "lexnet_weights.bin");
    return p;
}

static void run(const Net *net, const double *kc, const double *kb, const unsigned char *src, size_t n,
                unsigned char *cls, void *scratch) {
    if (use_interp) classify(net, src, n, cls, (double *)scratch);
    else classify_compiled(net, kc, kb, src, n, cls, (uint16_t *)scratch);
}

int main(int argc, char **argv) {
    int mode = 0, reps = 1;
    const char *path = NULL, *wpath = NULL;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--classes")) mode = 1;
        else if (!strcmp(argv[i], "--bench")) mode = 2, reps = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--interp")) use_interp = 1;
        else if (!strcmp(argv[i], "--dense")) use_dense = use_interp = 1;
        else if (!strcmp(argv[i], "-w")) wpath = argv[++i];
        else path = argv[i];
    }
    if (!path) { fprintf(stderr, "usage: lexnet [-w weights.bin] [--interp [--dense]] [--classes|--bench N] file.c\n"); return 2; }
    Net net = load(wpath ? wpath : default_weights(argv[0]));
    double kc[K_N_COEF], kb[K_N_BIAS];
    if (!use_interp) {
        uint64_t h = struct_hash(&net);
        if (h != K_STRUCT_HASH) {
            fprintf(stderr, "weights: architecture hash %016llx does not match compiled kernel %016llx; "
                    "regenerate lexnet_kernel.h (codegen.py) or run with --interp\n",
                    (unsigned long long)h, (unsigned long long)K_STRUCT_HASH);
            return 1;
        }
        gather(&net, kc, kb);
    }

    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); return 1; }
    fseek(f, 0, SEEK_END);
    size_t n = (size_t)ftell(f);
    fseek(f, 0, SEEK_SET);
    unsigned char *src = malloc(n + 1), *cls = malloc(n + 1);
    void *scratch = malloc((n + 1) * (size_t)net.n_fout * sizeof(double));   /* interp: feats; compiled: bits */
    if (fread(src, 1, n, f) != n) return 1;
    fclose(f);

    if (mode == 2) {
        struct timespec a, b;
        clock_gettime(CLOCK_MONOTONIC, &a);
        for (int i = 0; i < reps; i++) run(&net, kc, kb, src, n, cls, scratch);
        clock_gettime(CLOCK_MONOTONIC, &b);
        double sec = (b.tv_sec - a.tv_sec) + (b.tv_nsec - a.tv_nsec) * 1e-9;
        printf("%zu chars x %d: %.1f ms  (%.0f ns/char, %.1f M chars/s)\n",
               n, reps, sec * 1e3, sec / reps / n * 1e9, n * reps / sec / 1e6);
        return 0;
    }
    run(&net, kc, kb, src, n, cls, scratch);
    if (mode == 1) {
        for (size_t t = 0; t < n; t++) putchar("0123456789A"[cls[t]]);
        return 0;
    }
    int cur = -1;
    for (size_t t = 0; t < n; t++) {
        if (cls[t] != cur) { fputs("\x1b[0m", stdout); fputs(ANSI[cls[t]], stdout); cur = cls[t]; }
        putchar(src[t]);
    }
    fputs("\x1b[0m", stdout);
    return 0;
}
