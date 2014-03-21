if version < 600
  syn clear
elseif exists("b:current_syntax")
  finish
endif

syn keyword hottKeyword         pmap ext iso coe inv comp idp R
syn match   hottLineComment     "---*\([^-!#$%&\*\+./<=>\?@\\^|~].*\)\?$"
syn region  hottBlockComment    start="{-"  end="-}" contains=hottBlockComment
syn match   hottNumber          "\<[0-9]\+\>"
syn match   hottType            "\<Type[0-9]*\>"
syn match   hottType            "Nat"
" syn match   hottDelimiter       "(\|)\|;\|_\|{\|}"
syn match   hottOperator        "=\|:\|::\|,\|->\|*\|\\"

if version >= 508 || !exists("did_hott_syntax_inits")
  if version < 508
    let did_hott_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink hottKeyword        Keyword
  HiLink hottLineComment    hottComment
  HiLink hottBlockComment   hottComment
  HiLink hottComment        Comment
  HiLink hottNumber         Number
  HiLink hottType           Type
  HiLink hottDelimiter      Delimiter
  HiLink hottOperator       Operator

  delcommand HiLink
endif

let b:current_syntax = "hott"
