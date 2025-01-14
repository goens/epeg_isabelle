```
dotξ -> any [...]

  spaceξ -> any [' ', '\n', '\t',
                '(';'*'; ( (!('*';')')) ; any[dotξ,'\n','\t'])* ; '*';')']
  sξ -> spaceξ*

  digξ -> any ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

  alphξ -> any [...]

  word_boundaryξ -> !(alphξ / digξ / '_')

  characterξ -> '"' ; dotξ ; '"' ; word_boundaryξ

  identξ -> (!digξ) ; (alphξ / digξ / '_')+

  stringξ -> '\'' ; (!'\'';(identξ / dotξ))* ; '\''

  primary_expressionξ -> identξ; μ(primξ ↦ identξ) /
                         '\'' ; δ(('\'' / ε) ; ((!'\'') ; dotξ)*, s); '\''; μ(primξ ↦ γ(s)) /
                         δ(((!' ') ; dotξ)*, s); μ(primξ ↦γ(s))

  coqStringξ -> primary_expressionξ; μ(coqξ ↦ γ(coqξ) ; sξ ;
                γ(primξ)) ; (' ' ; (' '/'\t')* ; coqStringξ)?
  testCoqξ -> ε; μ(coqξ ↦ ε) ; coqStringξ

  seq_symbolξ -> ' ' / '\n' / '\t'

  notationξ -> 'N';'o';'t';'a';'t';'i';'o';'n';word_boundaryξ

  Term -> !ε

  notation_statementξ -> notationξ ; sξ ; '"'; μ(coqξ ↦ ε) ; sξ ;
                         coqStringξ; μ(Term ↦ γ(Term) / (γ(coqξ);'.')) ; '"' ; sξ ;
                         ':' ; '=' ; sξ ; (!'.' ;(dotξ / spaceξ))* ; '.'
  -- The RHS of ":=" is irrelevant to us

  coqCodeξ -> sξ ; ((notation_statementξ/Term);sξ)*
```