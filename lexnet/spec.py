"""Lexnet's highlighting policy on bytes (not an ISO C lexer).

Class IDs and colors from lexnet.c's ANSI table: plain=0 (default), keyword=1
(bold magenta), type=2 (cyan), function=3 (bold blue), identifier=4 (default),
number/constant=5 (yellow), string=6 / character=7 (green), comment=8
(dim italic white), preprocessor=9 (orange), punctuation=10 (gray).
Only ASCII letters, digits and underscore form identifiers. The stored word is
truncated to fourteen characters, deliberately matching the model's policy.
"""
PLAIN, KEYWORD, TYPE, FUNCTION, IDENTIFIER, NUMBER, STRING, CHAR, COMMENT, PREPROC, PUNCT = range(11)
KEYWORDS = set(b'''auto break case const continue default do else enum extern for
goto if inline register restrict return sizeof static struct switch typedef union
volatile while _Alignas _Alignof _Atomic _Generic _Noreturn _Static_assert
_Thread_local alignas alignof constexpr static_assert thread_local typeof'''.split())
TYPES = set(b'''char double float int long short signed unsigned void bool _Bool
_Complex size_t ssize_t intptr_t wchar_t time_t off_t pid_t int8_t int16_t int32_t
int64_t uint8_t uint16_t uint32_t uint64_t FILE va_list ptrdiff_t uintptr_t'''.split())
CONSTANTS = set(b'NULL nullptr true false EOF'.split())
WS = b' \t\r\v\f'

def classes(data):
    block = line = string = char = pp = escaped = slash = star = closed = False
    string_closed = char_closed = pp_backslash = was_word = was_number = False
    line_start = True
    word = b''; forward = []
    for c in data:
        nl, space = c == 10, c in WS
        letter = 65 <= c <= 90 or 97 <= c <= 122 or c == 95
        digit = 48 <= c <= 57
        wordchar = letter or digit
        in_block = block and not closed
        in_line = line and not nl
        in_string = string and not string_closed and not nl
        in_char = char and not char_closed and not nl
        in_pp = pp and (not nl or pp_backslash)
        open_block = slash and c == 42
        open_line = slash and c == 47
        block = in_block or open_block
        line = in_line or open_line
        closed = star and c == 47
        string = in_string or (c == 34 and not (in_block or in_line or in_char))
        char = in_char or (c == 39 and not (in_block or in_line or in_string))
        pp = in_pp or (c == 35 and line_start and not (in_block or in_line or in_string or in_char))
        string_closed = in_string and c == 34 and not escaped
        char_closed = in_char and c == 39 and not escaped
        escaped = (in_string or in_char) and c == 92 and not escaped
        star = in_block and c == 42
        slash = c == 47 and not (in_block or in_line or in_string or in_char or open_line)
        pp_backslash = in_pp and c == 92
        line_start = nl or (line_start and space)
        blocked = in_block or in_line or in_string or in_char
        continuing = was_word and wordchar
        starting = letter and not was_number
        is_word = (continuing or starting) and not blocked
        number = (wordchar or c == 46) and (was_number or digit) and not (continuing or starting or blocked)
        word = (word + bytes([c]) if was_word else bytes([c]))[:14] if is_word else b''
        forward.append((block or line, string, char, pp, is_word, number,
                        word in KEYWORDS, word in TYPES, word in CONSTANTS,
                        open_block or open_line, c == 47, space, nl, c == 40))
        was_word, was_number = is_word, number
    # Right-to-left context extends a word's final classification to its start,
    # repairs the first slash of a comment, and looks across spaces for '('.
    next_word = next_open = parens = kw = ty = const = fn = False
    result = []
    for comment, string, char, pp, word, num, k, t, v, opening, slash, space, nl, lp in reversed(forward):
        comment = comment or (slash and next_open)
        kw = word and (kw if next_word else k)
        ty = word and (ty if next_word else t)
        const = word and (const if next_word else v)
        fn = word and (fn if next_word else parens and not (k or t or v))
        parens = lp or (space and parens)
        # Head argmax, with the earlier class winning ties.
        if string: label = STRING
        elif char: label = CHAR
        elif comment: label = COMMENT
        elif pp: label = PREPROC
        elif kw: label = KEYWORD
        elif ty: label = TYPE
        elif fn: label = FUNCTION
        elif const or num: label = NUMBER
        elif word: label = IDENTIFIER
        elif space or nl: label = PLAIN
        else: label = PUNCT
        result.append(label)
        next_word, next_open = word, opening
    return bytes(reversed(result))
