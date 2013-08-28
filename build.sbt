name := "Regolic"

version := "0.1"

scalaVersion := "2.10.0"

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

parallelExecution in Test := false

libraryDependencies += "org.scalatest" % "scalatest_2.10" % "1.9.1" % "test"

scabolic <<= (baseDirectory, fullClasspath in Runtime) map { (base, cp) =>
  val template = """#!/bin/sh
java -classpath "%s" %s "$@"
"""
    val mainStr = "regolic.Main"
    val contents = template.format(cp.files.absString, mainStr)
    val out = base / "scabolic"
    IO.write(out, contents)
    out.setExecutable(true)
    out
}

cafesat <<= (baseDirectory, fullClasspath in Runtime) map { (base, cp) =>
  val template = """#!/bin/sh
java -classpath "%s" %s sat "$@"
"""
    val mainStr = "regolic.Main"
    val contents = template.format(cp.files.absString, mainStr)
    val out = base / "cafesat"
    IO.write(out, contents)
    out.setExecutable(true)
    out
}

// We keep the bottom section as a trophy of the epic battle with sbt in order
// to run a parser generator automatically before compile. Basically we are just
// trying to use a code generator before compiling actual code.
// Let this be the hallmark justifying the implementation of our own native parser

//libraryDependencies += "net.sf.squirrel-sql.thirdparty.non-maven" % "java-cup" % "11a"
//cleanFiles <+= baseDirectory { base => base / "regolic" }
//
//cleanFiles <+= baseDirectory { base => base / "lib" / "smt-parser.jar" }
//
//smtlibParser <<= (unmanagedJars in Compile, managedClasspath in Compile, baseDirectory) map { (unmanaged, managed, base) =>
//  val classpath: String = (unmanaged ++ managed).map(_.data).mkString(":")
//  val smtlibDir = base / "smt-parser"
//  val exitCode = Process("make CLASSPATH=" + classpath, smtlibDir) !;
//  if(exitCode != 0)
//    error("Failure")
//  val jar = smtlibDir / "smt-parser.jar"
//  val libJar = base / "lib" / "smt-parser.jar"
//  IO.copyFile(jar, libJar)
//  libJar
//}
//
//clean <<= (clean, baseDirectory) map { (c, base) =>
//  val smtlibDir = base / "smt-parser"
//  Process("make clean", smtlibDir) !;
//  c
//}
//
//sourceGenerators in Compile <+= (sourceManaged in Compile, baseDirectory, managedClasspath in Compile, unmanagedJars in Compile) map { (dir, base, managed, unmanaged) => 
//  val classpath: String = (unmanaged ++ managed).map(_.data).mkString(":")
//  val cacheDir = base / ".cache"
//  val file = dir / "smtlib"
//  val smtparserDir = base / "smt-parser"
//  val smtlibDir = smtparserDir / "smtlib"
//  val grammarFile: File = smtparserDir / "smtlib.cf"
//  val cachedOp = FileFunction.cached(cacheDir, FilesInfo.lastModified, FilesInfo.exists){ (in: Set[File]) =>
//    val cmdBnfc = "bnfc -java1.5 smtlib.cf"
//    Process(cmdBnfc, base / "smt-parser") !;
//    val cmdLex = "java -cp " + classpath + " JLex.Main " + (smtlibDir / "Yylex").toString
//    println("cmdLex: " + cmdLex)
//    cmdLex !; 
//    val cmdCup = "java -cp " + classpath + " java_cup.Main " + (smtlibDir / "smtlib.cup").toString
//    println("cmdLex: " + cmdCup)
//    cmdCup !;
//    "mv parser.java sym.java " + smtlibDir.toString !;
//    IO.move(smtlibDir, file)
//    (file ** "*.java").get.toSet
//  }
//  cachedOp(Set(grammarFile)).toSeq
//}
