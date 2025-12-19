if exists("b:current_syntax") | finish | endif

syn match ketteKeyword "\<\%(if\|call\|while\|match\)\>"
syn match ketteKeyword "\v%(^|\s)\zs\(call\)\ze%($|\s)"
syn match ketteBoolean "\<t\>"
syn match ketteBoolean "\<f\>"

syn match ketteSpecial "\<\%(traits\|universe\|std\)\>"

syn match ketteSelf "\<self\>"

"Matches = or := only when part of a definition
syn match ketteAssignment "\S\+\s\+\zs\%(=\|:=\)"

syn keyword ketteOperator dup drop swap over rot neq bi 2bi keep dip 2dip
syn match ketteOperator "\v%(^|\s)\zs([+\-*%=]|bi\@\|bi\*\|fixnum\+\|fixnum\-|fixnum\*\|fixnum\/\|fixnum\%\|fixnum\?|float\?|\>string)\ze%($|\s)"

" Trait Target (word before addTraitSlots)
syn match ketteTraitTarget "\S\+\ze\s\+addTraitSlots\>"
syn match ketteKeyword     "\<addTraitSlots\>"

" Defined here so it overwrites Specials/Operators (e.g. 'std =' becomes Blue)
syn match ketteSlotName "\S\+\ze\s\+\%(=\|:=\)"

syn match ketteNumber "\v%(\s|^)\zs\d+%(\.\d+)?\ze%(\s|$)"
syn region ketteString start=+"+ skip=+\\"+ end=+"+

" Parents
syn match ketteStarIdentifier "\S\+\*"

syn match ketteMethodDef  ":"
syn match ketteMethodEnd  ";"
syn match ketteTerminator "\."

" Delimiters
syn match ketteDelimiter "(|"
syn match ketteDelimiter "|)"
syn match ketteDelimiter "\["
syn match ketteDelimiter "\]"
syn match ketteDelimiter "\]"
syn match ketteDelimiter "\]"

syn keyword ketteTodo TODO FIXME NOTE contained
syn match   ketteLineComment "//.*" contains=ketteTodo

" Block comments (allow nesting)
syn region  ketteBlockComment start="/\*" end="\*/" contains=ketteTodo,ketteBlockComment

syn region ketteStackEffect start="(\s" end=")" contains=ketteStackDash
syn match  ketteStackDash "--" contained

hi def link ketteSlotName       Function
hi def link ketteAssignment     Operator

hi def link ketteTraitTarget    Structure
hi def link ketteStarIdentifier Type

hi def link ketteSelf           Type
hi def link ketteKeyword        Keyword
hi def link ketteBoolean        Boolean
hi def link ketteSpecial        Special

hi def link ketteOperator       Operator
hi def link ketteTerminator     Macro
hi def link ketteDelimiter      Delimiter
hi def link ketteMethodDef      Special
hi def link ketteMethodEnd      Special

hi def link ketteNumber         Number
hi def link ketteString         String

hi def link ketteLineComment    Comment
hi def link ketteBlockComment   Comment
hi def link ketteTodo           Todo
hi def link ketteStackEffect    SpecialComment
hi def link ketteStackDash      Operator

let b:current_syntax = "kette"
