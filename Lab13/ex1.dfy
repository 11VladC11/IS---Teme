// Ex1 b
method Max(x: int, y: int) returns (m: int)
  ensures m == if x > y then x else y
{
  if x > y {
    m := x;
  } else {
    m := y;
  }
}
// Ex1 a
method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == if x > y then x else y
{
  s := x + y;
  m := Max(x, y);
}
// Ex1 c
method Main()
{
  var s, m := MaxSum(1928, 1);
  print "Sum: ", s, "\n";
  print "Max: ", m, "\n";
}
