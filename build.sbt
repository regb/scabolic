name := "Regolic"

version := "0.1"

scalaVersion := "2.9.1"

scalacOptions ++= Seq("-unchecked", "-deprecation")

libraryDependencies += "org.scalatest" %% "scalatest" % "1.6.1" % "test"

testIntegration := { val exitCode = "./run-regression.sh" !; if(exitCode != 0) error("Failure") }
