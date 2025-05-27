theory ReCore_IFS
  imports SecurityModel Lang
begin

record  action = 
        actk :: " actk"
        eventof :: "('l,'k,'s, 'prog) event"
        domain ::  "'d"