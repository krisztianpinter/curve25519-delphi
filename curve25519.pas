unit curve25519;

interface

type
  b32 = packed array[0..31] of byte;

procedure crypto_scalarmult(out q: b32; const n, p: b32);

procedure crypto_scalarmult_base(out q: b32; const n: b32);


implementation

{$O+,Q-,R-}

type
  gf = array[0..15] of int64;

const
  _9: b32 = (9,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0);
  _121665: gf = ($DB41, $1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);

procedure car25519(var o: gf);
var
  i: integer;
  c, m: int64;
begin
  for i := 0 to 15 do begin
    c := (1 shl 16);
    o[i] := o[i] + c;
    c := o[i];
    m := -(c shr 63 and 1);
    c := m xor ((m xor c) shr 16); // arithmetic shift

    if i < 15 // fuck djb in particular
      then o[i+1] := o[i+1] + c - 1
      else o[0] := o[0] + 38*(c-1);

    o[i] := o[i] - c shl 16;
  end;
end;

procedure sel25519(var p: gf; var q: gf; b: integer);
var
  t, c: int64;
  i: integer;
begin
  c := b;
  c := not (c-1);
  for i := 0 to 15 do begin
    t := c and (p[i] xor q[i]);
    p[i] := p[i] xor t;
    q[i] := q[i] xor t;
  end;
end;

procedure pack25519(out o: b32; const n: gf);
var
  i, j, b: integer;
  m, t: gf;
begin
  for i := 0 to 15 do t[i] := n[i];
  car25519(t);
  car25519(t);
  car25519(t);
  for j := 0 to 1 do begin
    m[0] := t[0] - $ffed;
    for i := 1 to 14 do begin
      m[i] := t[i] - $ffff - ((m[i-1] shr 16) and 1);
      m[i-1] := m[i-1] and $ffff;
    end;
    m[15] := t[15] - $7fff - ((m[14] shr 16) and 1);
    b := (m[15] shr 16) and 1;
    m[14] := m[14] and $ffff;
    sel25519(t, m, 1-b);
  end;
  for i := 0 to 15 do begin
    o[2*i] := t[i] and $ff;
    o[2*i+1] := (t[i] shr 8) and $ff;
  end;
end;

procedure unpack25519(out o: gf; const n: b32);
var
  i: integer;
begin
  for i := 0 to 15 do o[i] := n[2*i] + (int64(n[2*i+1]) shl 8);
  o[15] := o[15] and $7fff;
end;

procedure AA(out o: gf; const a, b: gf);
var
  i: integer;
begin
  for i := 0 to 15 do o[i] := a[i] + b[i];
end;

procedure ZZ(out o: gf; const a, b: gf);
var
  i: integer;
begin
  for i := 0 to 15 do o[i] := a[i] - b[i];
end;

procedure MM(out o: gf; const a, b: gf);
var
  i, j: integer;
  t: array[0..30] of int64;
begin
  for i := 0 to 30 do t[i] := 0;
  for i := 0 to 15 do for j := 0 to 15 do t[i+j] := t[i+j] + a[i] * b[j];
  for i := 0 to 14 do t[i] := t[i] + 38 * t[i+16];
  for i := 0 to 15 do o[i] := t[i];
  car25519(o);
  car25519(o);
end;

procedure SS(out o:gf; const a: gf);
begin
  MM(o, a, a);
end;

procedure inv25519(out o: gf; const i: gf);
var
  c: gf;
  a: integer;
begin
  for a := 0 to 15 do c[a] := i[a];
  for a := 253 downto 0 do begin
    SS(c, c);
    if (a <> 2) and (a <> 4) then MM(c, c, i);
  end;
  for a := 0 to 15 do o[a] := c[a];
end;

procedure pow2523(out o: gf; const i: gf);
var
  c: gf;
  a: integer;
begin
  for a := 0 to 15 do c[a] := i[a];
  for a := 250 downto 0 do begin
    SS(c, c);
    if a <> 1 then MM(c, c, i);
  end;
  for a := 0 to 15 do o[a] := c[a];
end;

procedure crypto_scalarmult(out q: b32; const n, p: b32);
var
  z: b32;
  x, x16, x32, x48: gf;
  i, r: integer;
  a, b, c, d, e, f: gf;
begin
  for i:= 0 to 30 do z[i] := n[i];
  z[31] := (n[31] and 127) or 64;
  z[0]:= z[0] and 248;
  unpack25519(x, p);
  for i := 0 to 15 do begin
    a[i] := 0;
    b[i] := x[i];
    c[i] := 0;
    d[i] := 0;
  end;
  a[0] := 1;
  d[0] := 1;
  for i := 254 downto 0 do begin
    r := (z[i shr 3] shr (i and 7)) and 1;
    sel25519(a, b, r);
    sel25519(c, d, r);
    AA(e, a, c);
    ZZ(a, a, c);
    AA(c, b, d);
    ZZ(b, b, d);
    SS(d, e);
    SS(f, a);
    MM(a, c, a);
    MM(c, b, e);
    AA(e, a, c);
    ZZ(a, a, c);
    SS(b, a);
    ZZ(c, d, f);
    MM(a, c, _121665);
    AA(a, a, d);
    MM(c, c, a);
    MM(a, d, f);
    MM(d, b, x);
    SS(b, e);
    sel25519(a, b, r);
    sel25519(c, d, r);
  end;
  for i := 0 to 15 do begin
    x16[i] := a[i];
    x32[i] := c[i];
    x48[i] := b[i];
  end;
  inv25519(x32, x32);
  MM(x16, x16, x32);
  pack25519(q, x16);
end;

procedure crypto_scalarmult_base(out q: b32; const n: b32);
begin
  crypto_scalarmult(q, n, _9);
end;

end.
