name := "Regolic"

version := "0.1"

scalaVersion := "2.9.1"

scalacOptions ++= Seq("-unchecked", "-deprecation")

libraryDependencies += "org.scalatest" %% "scalatest" % "1.6.1" % "test"

TaskKey[File]("script") <<= (baseDirectory, fullClasspath in Runtime, mainClass in Runtime) map { (base, cp, main) =>
  val template = 
"""#!/bin/sh

java -classpath "%s" %s "$@"
"""
    val mainStr = main getOrElse error("No main class specified")
    val contents = template.format(cp.files.absString, mainStr)
    val out = base / "regolic"
    IO.write(out, contents)
    out.setExecutable(true)
    out
}
