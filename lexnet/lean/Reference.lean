/-
  lexnet, as a short program.  Nothing in this file mentions a weight, a network
  unit or a generated table.  It is a plain Lean port of `spec.py`.

  The highlighter assigns each input byte one of eleven classes.  It works in two
  passes.  A left-to-right pass tracks comments, strings, characters, preprocessor
  lines and the current word.  A right-to-left pass then gives a whole word the
  label decided at its last byte, repairs the first `/` of a comment opener, and
  looks ahead across blanks for the `(` that marks a function name.
-/
namespace Ref

abbrev Byte := Fin 256

/-- The eleven classes. -/
def plain : Nat := 0
def keyword : Nat := 1
def type : Nat := 2
def function : Nat := 3
def identifier : Nat := 4
def number : Nat := 5
def string : Nat := 6
def character : Nat := 7
def comment : Nat := 8
def preprocessor : Nat := 9
def punctuation : Nat := 10

/-! ### Byte predicates (ASCII only) -/
def isNewline (c : Nat) : Bool := c == 10
def isBlank (c : Nat) : Bool := c == 32 || c == 9 || c == 13 || c == 11 || c == 12
def isLetter (c : Nat) : Bool :=
  (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95   -- A-Z a-z _
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def isWordChar (c : Nat) : Bool := isLetter c || isDigit c

/-! ### Name lists.  Only the first 14 bytes of a word are remembered. -/
def bytes (s : String) : List Nat := s.toList.map Char.toNat

def keywords : List (List Nat) := ([
  "auto", "break", "case", "const", "continue", "default", "do", "else", "enum",
  "extern", "for", "goto", "if", "inline", "register", "restrict", "return",
  "sizeof", "static", "struct", "switch", "typedef", "union", "volatile", "while",
  "_Alignas", "_Alignof", "_Atomic", "_Generic", "_Noreturn", "_Static_assert",
  "_Thread_local", "alignas", "alignof", "constexpr", "static_assert",
  "thread_local", "typeof"] : List String).map bytes

def types : List (List Nat) := ([
  "char", "double", "float", "int", "long", "short", "signed", "unsigned", "void",
  "bool", "_Bool", "_Complex", "size_t", "ssize_t", "intptr_t", "wchar_t", "time_t",
  "off_t", "pid_t", "int8_t", "int16_t", "int32_t", "int64_t", "uint8_t",
  "uint16_t", "uint32_t", "uint64_t", "FILE", "va_list", "ptrdiff_t",
  "uintptr_t"] : List String).map bytes

def constants : List (List Nat) :=
  (["NULL", "nullptr", "true", "false", "EOF"] : List String).map bytes

/-! ### Left-to-right pass -/

/-- What the left-to-right pass remembers between bytes. -/
structure Left where
  block : Bool := false          -- inside or opening a /* comment
  line : Bool := false           -- inside or opening a // comment
  inStr : Bool := false
  inChr : Bool := false
  pp : Bool := false             -- inside a preprocessor line
  escaped : Bool := false        -- previous byte was an unescaped backslash in a literal
  slash : Bool := false          -- previous byte was a `/` that may open a comment
  star : Bool := false           -- previous byte was a `*` inside a block comment
  closed : Bool := false         -- previous byte closed a block comment
  strClosed : Bool := false
  chrClosed : Bool := false
  ppBackslash : Bool := false
  wasWord : Bool := false
  wasNumber : Bool := false
  lineStart : Bool := true
  word : List Nat := []          -- the current word, at most 14 bytes

/-- What the left-to-right pass says about one byte. -/
structure Seen where
  comment : Bool
  string : Bool
  char : Bool
  pp : Bool
  word : Bool
  number : Bool
  isKeyword : Bool
  isType : Bool
  isConstant : Bool
  opener : Bool     -- this byte is the second byte of `/*` or `//`
  slash : Bool
  blank : Bool
  newline : Bool
  paren : Bool      -- this byte is `(`

def step (s : Left) (c : Nat) : Left × Seen :=
  let nl := isNewline c
  let blank := isBlank c
  let letter := isLetter c
  let digit := isDigit c
  let wordChar := isWordChar c
  let inBlock := s.block && !s.closed
  let inLine := s.line && !nl
  let inStr := s.inStr && !s.strClosed && !nl
  let inChr := s.inChr && !s.chrClosed && !nl
  let inPP := s.pp && (!nl || s.ppBackslash)
  let openBlock := s.slash && c == 42
  let openLine := s.slash && c == 47
  let blocked := inBlock || inLine || inStr || inChr
  let continuing := s.wasWord && wordChar
  let starting := letter && !s.wasNumber
  let isWord := (continuing || starting) && !blocked
  let isNumber := (wordChar || c == 46) && (s.wasNumber || digit) &&
                  !(continuing || starting || blocked)
  let word := if isWord then ((if s.wasWord then s.word ++ [c] else [c]).take 14) else []
  let next : Left :=
    { block := inBlock || openBlock
      line := inLine || openLine
      inStr := inStr || (c == 34 && !(inBlock || inLine || inChr))
      inChr := inChr || (c == 39 && !(inBlock || inLine || inStr))
      pp := inPP || (c == 35 && s.lineStart && !blocked)
      escaped := (inStr || inChr) && c == 92 && !s.escaped
      slash := c == 47 && !(blocked || openLine)
      star := inBlock && c == 42
      closed := s.star && c == 47
      strClosed := inStr && c == 34 && !s.escaped
      chrClosed := inChr && c == 39 && !s.escaped
      ppBackslash := inPP && c == 92
      wasWord := isWord
      wasNumber := isNumber
      lineStart := nl || (s.lineStart && blank)
      word := word }
  (next,
   { comment := next.block || next.line, string := next.inStr, char := next.inChr
     pp := next.pp, word := isWord, number := isNumber
     isKeyword := keywords.contains word, isType := types.contains word
     isConstant := constants.contains word
     opener := openBlock || openLine, slash := c == 47, blank := blank
     newline := nl, paren := c == 40 })

def forwardPass : Left → List Byte → List Seen
  | _, [] => []
  | s, b :: bs => let (s', seen) := step s b.val; seen :: forwardPass s' bs

/-! ### Right-to-left pass -/

/-- What the right-to-left pass remembers about the bytes to its right. -/
structure Right where
  nextWord : Bool := false      -- the next byte is part of a word
  nextOpener : Bool := false    -- the next byte completes a comment opener
  paren : Bool := false         -- a `(` follows, possibly after blanks
  keyword : Bool := false       -- the word starting at the next byte is a keyword
  type : Bool := false
  constant : Bool := false
  function : Bool := false

def label (c : Seen) (r : Right) : Right × Nat :=
  let comment := c.comment || (c.slash && r.nextOpener)
  let keyword := c.word && (if r.nextWord then r.keyword else c.isKeyword)
  let type := c.word && (if r.nextWord then r.type else c.isType)
  let constant := c.word && (if r.nextWord then r.constant else c.isConstant)
  let function := c.word &&
    (if r.nextWord then r.function else r.paren && !(c.isKeyword || c.isType || c.isConstant))
  let answer : Nat :=
    if c.string then string
    else if c.char then character
    else if comment then Ref.comment
    else if c.pp then preprocessor
    else if keyword then Ref.keyword
    else if type then Ref.type
    else if function then Ref.function
    else if constant || c.number then number
    else if c.word then identifier
    else if c.blank || c.newline then plain
    else punctuation
  ({ nextWord := c.word, nextOpener := c.opener, paren := c.paren || (c.blank && r.paren),
     keyword := keyword, type := type, constant := constant, function := function }, answer)

/-- Walk the right-to-left pass: result is the state at the left end and the labels. -/
def backwardPass : List Seen → Right × List Nat
  | [] => ({}, [])
  | c :: cs => let (r, rest) := backwardPass cs; let (r', a) := label c r; (r', a :: rest)

/-- The whole highlighter: one class per input byte. -/
def referenceClasses (bs : List Byte) : List Nat :=
  (backwardPass (forwardPass {} bs)).2

end Ref
