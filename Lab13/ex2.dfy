function Max(a: int, b: int): int
  ensures Max(a, b) >= a && Max(a, b) >= b
  ensures Max(a, b) == a || Max(a, b) == b
{
  if a >= b then a else b
}

method MaxSum(x: int, y: int) returns (s: int, m: int)
  ensures s == x + y
  ensures m == Max(x, y)
{
  s := x + y;
  if x >= y {
    m := x;
  } else {
    m := y;
  }
}

method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
  requires m <= s <= 2*m
  ensures s == x + y
  ensures m == x || m == y
  ensures x <= m && y <= m
{
  x := m;
  y := s - m;
}

method TestMaxSum(x: int, y: int)
{
  var s, m := MaxSum(x, y);
  assume m <= s <= 2*m;
  var xx, yy := ReconstructFromMaxSum(s, m);
  assert (xx == x && yy == y) || (xx == y && yy == x);
}

method Caller() {
  var x := 1928;
  var y := 1;

  var sum, maximum := MaxSum(x, y);

  assert sum == x + y;
  assert maximum == Max(x, y); // Max este funcție, se verifică corect
}
