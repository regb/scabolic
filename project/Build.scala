import sbt._
import Keys._

object Regolic extends Build {

  //val testIntegration: TaskKey[Unit] = TaskKey[Unit]("test-integration", "Execute integration tests")
  //val testAll: TaskKey[Unit] = TaskKey[Unit]("test-all", "Execute unit and integration tests")
  //val smtlibParser: TaskKey[File] = TaskKey[File]("smtlib-parser", "Build the smtlib parser")
  val scabolic: TaskKey[File] = TaskKey[File]("scabolic", "Create the main run script")
  val cafesat: TaskKey[File] = TaskKey[File]("cafesat", "Create the sat solver script")

  //val testIntegrationTask = testIntegration <<= (compile in Compile, baseDirectory, script) map { (_, base, _) => 
  //  val exitCode = base + "/scripts/run-regression.sh" !;
  //  if(exitCode != 0) sys.error("Failure")
  //}
  //val testAllTask = testAll <<= (test in Test, testIntegration) map { (_, _) => ()}


  lazy val root = 
    Project("root", file("."), settings = Project.defaultSettings).dependsOn(Projects.depProject)
}

object V {
  val depProject = "004fab30fc294677a14429fad2cd95ab4d366416"
}

object Projects {
  lazy val depProject = RootProject(uri("git://github.com/regb/scala-smtlib.git#%s".format(V.depProject)))
}
