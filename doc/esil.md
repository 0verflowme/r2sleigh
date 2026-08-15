ESIL -- Evaluable Strings Intermediate Language
=================================================

Background
----------

ESIL is radare2's stack-based, RPN evaluation language for instruction
semantics. r2sleigh generates ESIL from R2IL operations for backward
compatibility with radare2's ESIL-based analysis passes.

See the [radare2 book](https://book.rada.re/disassembling/esil.html) for
full ESIL documentation. The generation code lives in
`r2sleigh-lift/src/esil.rs`.

ESIL Syntax Summary
--------------------

| Syntax | Meaning |
|--------|---------|
| `a,b,+` | Push a, push b, add |
| `a,b,=` | b = a (assignment -- note reversed order) |
| `a,[N]` | Read N bytes from memory address a |
| `a,b,=[N]` | Write N bytes of b to memory address a |
| `a,?{,x,}` | If a is nonzero then execute x |

R2ILOp to ESIL Translation Table
---------------------------------

| R2ILOp | ESIL Output | Notes |
|--------|-------------|-------|
| Copy | `src,dst,=` | |
| Load | `addr,[N],dst,=` | N = dst.size |
| Store | `val,addr,=[N]` | N = val.size |
| IntAdd | `a,b,+,dst,=` | |
| IntSub | `a,b,-,dst,=` | ASCII 0x2D only |
| IntMult | `a,b,*,dst,=` | |
| IntDiv | `a,b,/,dst,=` | |
| IntRem | `a,b,%,dst,=` | |
| IntNegate | `src,0,-,dst,=` | Two's complement |
| IntAnd | `a,b,&,dst,=` | |
| IntOr | `a,b,\|,dst,=` | Bitwise OR |
| IntXor | `a,b,^,dst,=` | |
| IntNot | `src,~,dst,=` | Bitwise NOT (not !) |
| IntLeft | `a,b,<<,dst,=` | Left shift |
| IntRight | `a,b,>>,dst,=` | Logical shift right |
| IntSRight | `a,b,>>>,dst,=` | Arithmetic shift right |
| IntEqual | `a,b,==,dst,=` | |
| IntLess | `a,b,<,dst,=` | Unsigned |
| IntSLess | `a,b,<$,dst,=` | Signed |
| IntZExt | `src,dst,=` | Implicit in ESIL |
| IntSExt | `src,bits,~~,dst,=` | Sign extension |
| Branch | `target,pc,=` | |
| CBranch | `cond,?{,target,pc,=,}` | |
| Call | `target,pc,=` | |
| Return | `target,pc,=` | |

CallOther operations map to `CALLOTHER(<numeric-id>)`. The identifier comes
directly from the loaded Sleigh translator. Ambient specification files and
presentation labels do not alter ESIL or lifted semantics.

ESIL Pitfalls
-------------

**Unicode minus**: Always use ASCII `-` (0x2D). Unicode minus (U+2212) breaks
evaluation.

**Sign extension**: Uses `~~` operator (`value,bits,~~`). Do not confuse with
bitwise NOT `~`.

**Shift operators**: Arithmetic shift right is `>>>`, NOT `>>>>`.

**Width handling**: ESIL has no explicit widths. Subpiece and other width-
changing ops require explicit masking.

**Boolean vs bitwise NOT**: `~` flips all bits. `!` is boolean (0/nonzero).

Example
-------

`mov rax, [rbp-8]` produces:

```
rbp,0xfffffffffffffff8,+,[8],rax,=
```

Plugin Integration
------------------

The plugin's `sleigh_op` callback writes ESIL into `RAnalOp.esil` during
`aaa` analysis, making Sleigh-based lifting available to all radare2 ESIL
consumers.
