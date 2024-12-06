plugins {
    // Apply the application plugin to add support for building a CLI application in Java.
    application
}

repositories {
    // Use Maven Central for resolving dependencies.
    mavenCentral()
}

dependencies {
    // Development dependencies
    implementation("org.jetbrains:annotations:24.0.0")
    implementation("com.google.guava:guava:33.2.1-jre")
    implementation("org.jline:jline:3.26.1")

    // Testing dependencies
    testImplementation("org.junit.jupiter:junit-jupiter:5.10.2")
    testRuntimeOnly("org.junit.platform:junit-platform-launcher")
}

// Apply a specific Java toolchain to ease working on different environments.
java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(22))
    }
}

application {
    // Define the main class for the application.
    mainClass.set("cora.App")

    //Sets the application DefaultJVMArgs
    applicationDefaultJvmArgs = listOf("--enable-preview")
}

tasks {
    // Compiler options with preview java features enabled
    val COMPILER_OPTIONS =
        listOf("--enable-preview", "-Xlint:preview", "-Xlint:deprecation", "-Xlint:unchecked")

    withType<JavaCompile>() {
        options.compilerArgs = COMPILER_OPTIONS;
        options.encoding = "UTF8"
    }

    named<Test>("test") {
        // Use JUnit Platform for unit tests.
        useJUnitPlatform()
        jvmArgs = listOf("--enable-preview")
    }

    named<JavaExec>("run") {
        jvmArgs = listOf("--enable-preview")
    }
}
