Class Test := { wit : nat }.

Set Warnings "+deprecated-instance-without-locality".
Fail Instance test: Test.
