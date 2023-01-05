MODULE BigSample;

  PROCEDURE Multiply;

    VAR x, y, z: INTEGER;

  BEGIN Read(x); Read(y); z := 0;
    WHILE x > 0 DO
      IF x MOD 2 = 1 THEN z := z + y END;
      y := 2 * y; x := x DIV 2
    END;
    Write(x); Write(y); Write(z); WriteLn
  END Multiply;

  PROCEDURE Divide;

    VAR x, y, r, q, w: INTEGER;

  BEGIN Read(x); Read(y); r := x; q := 0; w := y;
    WHILE w <= r DO w := 2 * w END;
    WHILE w > y DO
      q := 2 * q; w := w DIV 2;
      IF w <= r THEN r := r - w; q := q + 1 END
    END;
    Write(x); Write(y); Write(q); Write(r); WriteLn
  END Divide;

  PROCEDURE BinSearch;

    VAR i, j, k, n, x: INTEGER;
      a: ARRAY 32 OF INTEGER;

  BEGIN Read(n); k := 0;
    WHILE k < n DO Read(a[k]); k := k + 1 END;
    i := 0; j := n;
    Read(x);
    WHILE i < j DO
      k := (i + j) DIV 2;
      IF x <= a[k] THEN j := k ELSE i := k + 1 END
    END;
    Write(i); Write(j); Write(a[j]); WriteLn
  END BinSearch;

  PROCEDURE Multiply1;

    VAR x, y, z: INTEGER;

  BEGIN Read(x); Read(y); z := 0;
    WHILE x > 0 DO
      IF x MOD 2 = 1 THEN z := z + y END;
      y := 2 * y; x := x DIV 2
    END;
    Write(x); Write(y); Write(z); WriteLn
  END Multiply1;

  PROCEDURE Divide1;

    VAR x, y, r, q, w: INTEGER;

  BEGIN Read(x); Read(y); r := x; q := 0; w := y;
    WHILE w <= r DO w := 2 * w END;
    WHILE w > y DO
      q := 2 * q; w := w DIV 2;
      IF w <= r THEN r := r - w; q := q + 1 END
    END;
    Write(x); Write(y); Write(q); Write(r); WriteLn
  END Divide1;

  PROCEDURE BinSearch1;

    VAR i, j, k, n, x: INTEGER;
      a: ARRAY 32 OF INTEGER;

  BEGIN Read(n); k := 0;
    WHILE k < n DO Read(a[k]); k := k + 1 END;
    i := 0; j := n;
    Read(x);
    WHILE i < j DO
      k := (i + j) DIV 2;
      IF x <= a[k] THEN j := k ELSE i := k + 1 END
    END;
    Write(i); Write(j); Write(a[j]); WriteLn
  END BinSearch1;

  PROCEDURE Example;

    PROCEDURE Multiply;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply;

    PROCEDURE Divide;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide;

    PROCEDURE BinSearch;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch;

    PROCEDURE Multiply1;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply1;

    PROCEDURE Divide1;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide1;

    PROCEDURE BinSearch1;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch1;

  END Example;

  PROCEDURE Example1;

    PROCEDURE Multiply;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply;

    PROCEDURE Divide;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide;

    PROCEDURE BinSearch;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch;

    PROCEDURE Multiply1;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply1;

    PROCEDURE Divide1;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide1;

    PROCEDURE BinSearch1;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch1;

  END Example1;

  PROCEDURE Example2;

    PROCEDURE Multiply;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply;

    PROCEDURE Divide;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide;

    PROCEDURE BinSearch;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch;

    PROCEDURE Multiply1;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply1;

    PROCEDURE Divide1;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide1;

    PROCEDURE BinSearch1;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch1;

  END Example2;

  PROCEDURE BigExample;

    PROCEDURE Multiply;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply;

    PROCEDURE Divide;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide;

    PROCEDURE BinSearch;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch;

    PROCEDURE Multiply1;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply1;

    PROCEDURE Divide1;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide1;

    PROCEDURE BinSearch1;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch1;

    PROCEDURE Example;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example;

    PROCEDURE Example1;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example1;

    PROCEDURE Example2;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example2;

  END BigExample;

  PROCEDURE BigExample1;

    PROCEDURE Multiply;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply;

    PROCEDURE Divide;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide;

    PROCEDURE BinSearch;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch;

    PROCEDURE Multiply1;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply1;

    PROCEDURE Divide1;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide1;

    PROCEDURE BinSearch1;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch1;

    PROCEDURE Example;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example;

    PROCEDURE Example1;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example1;

    PROCEDURE Example2;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example2;

  END BigExample1;

  PROCEDURE BigExample2;

    PROCEDURE Multiply;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply;

    PROCEDURE Divide;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide;

    PROCEDURE BinSearch;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch;

    PROCEDURE Multiply1;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply1;

    PROCEDURE Divide1;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide1;

    PROCEDURE BinSearch1;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch1;

    PROCEDURE Example;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example;

    PROCEDURE Example1;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example1;

    PROCEDURE Example2;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example2;

  END BigExample2;

  PROCEDURE BigExample3;

    PROCEDURE Multiply;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply;

    PROCEDURE Divide;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide;

    PROCEDURE BinSearch;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch;

    PROCEDURE Multiply1;

      VAR x, y, z: INTEGER;

    BEGIN Read(x); Read(y); z := 0;
      WHILE x > 0 DO
        IF x MOD 2 = 1 THEN z := z + y END;
        y := 2 * y; x := x DIV 2
      END;
      Write(x); Write(y); Write(z); WriteLn
    END Multiply1;

    PROCEDURE Divide1;

      VAR x, y, r, q, w: INTEGER;

    BEGIN Read(x); Read(y); r := x; q := 0; w := y;
      WHILE w <= r DO w := 2 * w END;
      WHILE w > y DO
        q := 2 * q; w := w DIV 2;
        IF w <= r THEN r := r - w; q := q + 1 END
      END;
      Write(x); Write(y); Write(q); Write(r); WriteLn
    END Divide1;

    PROCEDURE BinSearch1;

      VAR i, j, k, n, x: INTEGER;
        a: ARRAY 32 OF INTEGER;

    BEGIN Read(n); k := 0;
      WHILE k < n DO Read(a[k]); k := k + 1 END;
      i := 0; j := n;
      Read(x);
      WHILE i < j DO
        k := (i + j) DIV 2;
        IF x <= a[k] THEN j := k ELSE i := k + 1 END
      END;
      Write(i); Write(j); Write(a[j]); WriteLn
    END BinSearch1;

    PROCEDURE Example;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example;

    PROCEDURE Example1;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example1;

    PROCEDURE Example2;

      PROCEDURE Multiply;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply;

      PROCEDURE Divide;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide;

      PROCEDURE BinSearch;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch;

      PROCEDURE Multiply1;

        VAR x, y, z: INTEGER;

      BEGIN Read(x); Read(y); z := 0;
        WHILE x > 0 DO
          IF x MOD 2 = 1 THEN z := z + y END;
          y := 2 * y; x := x DIV 2
        END;
        Write(x); Write(y); Write(z); WriteLn
      END Multiply1;

      PROCEDURE Divide1;

        VAR x, y, r, q, w: INTEGER;

      BEGIN Read(x); Read(y); r := x; q := 0; w := y;
        WHILE w <= r DO w := 2 * w END;
        WHILE w > y DO
          q := 2 * q; w := w DIV 2;
          IF w <= r THEN r := r - w; q := q + 1 END
        END;
        Write(x); Write(y); Write(q); Write(r); WriteLn
      END Divide1;

      PROCEDURE BinSearch1;

        VAR i, j, k, n, x: INTEGER;
          a: ARRAY 32 OF INTEGER;

      BEGIN Read(n); k := 0;
        WHILE k < n DO Read(a[k]); k := k + 1 END;
        i := 0; j := n;
        Read(x);
        WHILE i < j DO
          k := (i + j) DIV 2;
          IF x <= a[k] THEN j := k ELSE i := k + 1 END
        END;
        Write(i); Write(j); Write(a[j]); WriteLn
      END BinSearch1;

    END Example2;

  END BigExample3;

END BigSample.

(*
OSP.Compile @
OSP.Decode
OSP.Load
OSP.Exec Multiply 47 11
OSP.Exec Divide 47 11
OSP.Exec BinSearch 5  1 3 5 7 9  4
OSP.Exec BinSearch 5  1 3 5 7 9  5
*)
