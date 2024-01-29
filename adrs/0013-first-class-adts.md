
Motivating example: _write_coin_

Can use pattern of reading expected value from a witness and write to a state. Need to get the value of where the coin
is at runtime and immediately write it to the state. We have specific operations for this. Might want to do other things
with coin types, like storing them in a struct.

Problem statement:

Remove special case handling of qualified coin info.