# Quorph Pipeline Surface Syntax — EBNF (locked)

This EBNF documents the **paper-facing** syntax supported by the validator artifact.
Logical operators are the keywords **`and`** and **`or`** (not `&&`/`||`). String
literals use **double quotes** only.

```
query      ::= "from" ident "in" source { newline "|" stage } ;

source     ::= ident ;              (* a named collection/table *)

stage      ::= "where" bexpr
             | "join" ident "in" source "on" bexpr
             | "select" record
             | "group by" expr "aggregate" "{" agg_fields "}"
             | "order by" id_list
             | "limit" INT ;

record     ::= "{" rec_fields "}" ;
rec_fields ::= rec_field { "," rec_field } ;
rec_field  ::= ident ":" expr ;

agg_fields ::= agg_field { "," agg_field } ;
agg_field  ::= ident ":" fn_call ;

id_list    ::= ident { "," ident } ;

expr       ::= bexpr ;

bexpr      ::= bexpr "or" bterm | bterm ;
bterm      ::= bterm "and" bfactor | bfactor ;
bfactor    ::= cexpr | "(" bexpr ")" ;

cexpr      ::= cexpr comp_op cterm | cterm ;
cterm      ::= primary ;

comp_op    ::= "!=" | ">=" | "<=" | "=" | ">" | "<" ;

primary    ::= INT | BOOL | STRING
             | dotted_ident
             | record
             | fn_call ;

dotted_ident ::= ident { "." ident } ;

fn_call    ::= ident "(" [ expr_list ] ")" ;
expr_list  ::= expr { "," expr } ;

ident      ::= /[A-Za-z_][A-Za-z0-9_]*/ ;
INT        ::= /-?[0-9]+/ ;
BOOL       ::= "true" | "false" ;
STRING     ::= '\"' ( [^\"\\] | '\\' [\"\\nrt] )* '\"' ;

newline    ::= (LF | CRLF)+ ;
```

**Join grammar (locked):**
```
join <var> in <source> on <bexpr>
```
- `<var>` binds the right-side tuple variable used in `<bexpr>`.
- `<source>` is a named collection present in the context.
- `<bexpr>` can reference both the left stream variable (from `from …`) and `<var>`. 
