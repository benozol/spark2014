package body Rep is

    task body TT is
       X : Boolean := False;
    begin
       loop
          X := not X;
       end loop;
    end;

end;
