(identifier) @Identifier

((identifier) @Keyword
 (#any-of? @Keyword if self when unless 4drop dip 2dip 3dip 4dip keep 2keep 3keep 4keep 
    bi 2bi "bi*" "2bi*" "bi@" "2bi@" tri "tri*" "tri@" get set unbox slot set-slot set-u8 get-u8 ">box"
    "(call)" call ">r" "r>" "r@"))

((identifier) @Function
  (#any-of? @Function "+" "-" "*" "/" "not" "neg" map zip each "ref-eq?"))

((identifier) @Repeat
 (#match? @Repeat "loop|while"))

; Booleans
((identifier) @Boolean
 (#any-of? @Boolean "f" "t"))

((identifier) @Operator
  (#any-of? @Operator dup 2dup 3dup 4dup dupd drop 2drop 3drop dropd swap swapd 2swap over overd rot -rot pick rotd -rotd roll -roll))

((identifier) @Punctuation.Special.Query
  (#any-of? @Punctuation.Special.Query "(new-boa)" "(new)" new new-boa "(special)" "(clone)" 
    "<array>" "<bytearray>" "resize-array" "resize-bytearray" "copy-array" "copy-bytearray"
    1array 2array 3array 4array 5array
    "array>obj" "obj>array"))

((identifier) @Function.Builtin
  (#any-of? @Function.Builtin "\\" "\\s" "@read-next" "@parse-int" "@parse-int" "@read-until" "@parse-until" "@skip-whitespace" "obj>map" ))

((identifier) @Variable.Builtin
  (#any-of? @Variable.Builtin self))

((identifier) @type
 (#match? @type "^#"))

(syntax_definition
  "@:" @Keyword
  (identifier) @Function.Builtin
  ";" @Keyword)

(word_definition
    ":" @Keyword
    (identifier) @Function
    ";"@Keyword)

(type_definition
  "type:" @Keyword
  (identifier) @Type
  ";" @Keyword)

(symbol_definition
  "$:" @Keyword
  (identifier) @Type)

(constant_definition
  "!:" @Keyword
  (identifier) @Function.Builtin)

(number) @Number
; Existing patterns from your query (unchanged)
(string) @String

[ ":" ";" "[" "]" "{" "}" ] @Delimiter

(line_comment) @Comment
(block_comment) @Comment
(stack_effect) @Comment
(todo_definition) @PreProc
