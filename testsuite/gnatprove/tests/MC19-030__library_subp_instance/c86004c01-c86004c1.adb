SEPARATE (C86004C01)
PROCEDURE C86004C1 IS
BEGIN
     IF B /= STANDARD.C86004C0(0) THEN
          return;
     END IF;

     IF A /= STANDARD.C86004C0(10) THEN
          return;
     END IF;

     return;
END C86004C1;
