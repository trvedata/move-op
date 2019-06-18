scalaVersion := "2.12.8"
name := "move-op"
organization := "com.martinkl.crdts"
version := "1.0"
libraryDependencies += "io.dropwizard.metrics" % "metrics-core" % "4.1.0"
libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.26"

enablePlugins(AkkaGrpcPlugin)
// ALPN agent
enablePlugins(JavaAgent)
javaAgents += "org.mortbay.jetty.alpn" % "jetty-alpn-agent" % "2.0.9" % "runtime;test"
