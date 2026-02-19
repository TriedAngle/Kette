if exists("b:current_syntax")
  finish
endif

syn keyword ketteKeyword resend
syn keyword ketteSelf self
syn keyword ketteLiteral True False None true false

syn match ketteAssign ":="
syn match ketteEquals "="
syn match ketteReturn "\^"
syn match kettePathSep "::"

syn match ketteDelimiter "[()\[\]{}|.;]"

syn region ketteString start=+"+ skip=+\\.+ end=+"+

syn match ketteRadixNumber "\<[+-]\=\d\+[rR][0-9A-Fa-f_]\+\>"
syn match ketteFloat "\<[+-]\=\d[0-9_]*\.[0-9_][0-9_]*\([eE][+-]\=[0-9_][0-9_]*\)\=\>"
syn match ketteFloat "\<[+-]\=\d[0-9_]*[eE][+-]\=[0-9_][0-9_]*\>"
syn match ketteNumber "\<[+-]\=\d[0-9_]*\>"

syn match ketteQualifiedPath "\<[A-Za-z_][A-Za-z0-9_]*\(::[A-Za-z_][A-Za-z0-9_]*\)\+\>"
syn match ketteKeywordPart "\<[A-Za-z_][A-Za-z0-9_]*:\ze\([^:]\|$\)"
syn match ketteIdentifier "\<[A-Za-z_][A-Za-z0-9_]*\>"

syn match ketteOperator "[!@#$%&*+\-=/~?<>,'`\\|][!@#$%&*+\-=/~?<>,'`\\|]*"

syn keyword ketteTodo TODO FIXME NOTE XXX contained
syn match ketteLineComment "//.*" contains=ketteTodo
syn region ketteBlockComment start="/\*" end="\*/" contains=ketteTodo,ketteBlockComment

hi def link ketteKeyword Keyword
hi def link ketteSelf Special
hi def link ketteLiteral Number
hi def link ketteAssign Operator
hi def link ketteEquals Operator
hi def link ketteReturn Special
hi def link kettePathSep Delimiter
hi def link ketteDelimiter Delimiter
hi def link ketteString String
hi def link ketteRadixNumber Number
hi def link ketteFloat Float
hi def link ketteNumber Number
hi def link ketteKeywordPart Function
hi def link ketteQualifiedPath Type
hi def link ketteIdentifier Identifier
hi def link ketteOperator Operator
hi def link ketteLineComment Comment
hi def link ketteBlockComment Comment
hi def link ketteTodo Todo

let b:current_syntax = "kette"
