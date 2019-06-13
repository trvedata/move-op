scalaVersion := "2.12.8"
name := "move-op"
organization := "com.martinkl.crdts"
version := "1.0"
//libraryDependencies += "org.typelevel" %% "cats-core" % "1.6.0"

enablePlugins(AkkaGrpcPlugin)
// ALPN agent
enablePlugins(JavaAgent)
javaAgents += "org.mortbay.jetty.alpn" % "jetty-alpn-agent" % "2.0.9" % "runtime;test"
