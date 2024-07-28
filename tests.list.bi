:i count 1
:b shell 53
cargo run -q -- lex tests/lex/floats.dark 2>/dev/null
:i returncode 0
:b stdout 440
1:1	literal	1
2:1	literal	1f
3:1	literal	0.2f
4:1	literal	1.2f
5:1	literal	1.23f
6:1	literal	1.2f
6:4	symbol	Field
7:1	literal	1.2f
7:4	word	abc
8:1	literal	1.2f
8:5	word	abc
9:1	literal	1
9:3	literal	0.2f
9:6	word	abc
10:1	literal	0.1f
10:4	symbol	RangeSpec
10:6	literal	2
10:8	word	abc
11:1	symbol	op Sub
11:2	literal	0.2f
11:5	symbol	op Sub
11:6	literal	23.33f
11:12	symbol	op Sub
11:13	literal	23f
11:16	symbol	op Sub
11:17	literal	33


:b stderr 0

