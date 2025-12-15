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
    implementation("org.jline:jline:3.26.1")

    // Testing dependencies
    testImplementation("org.junit.jupiter:junit-jupiter:5.10.2")
    testRuntimeOnly("org.junit.platform:junit-platform-launcher")
}

// Apply a specific Java toolchain to ease working on different environments.
java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(21))
    }
    sourceCompatibility = JavaVersion.VERSION_21
    targetCompatibility = JavaVersion.VERSION_21
}

application {
    // Define the main class for the application.
    mainClass.set("cora.App")

    //Sets the application DefaultJVMArgs
    applicationDefaultJvmArgs = listOf()
}

tasks {
    // Compiler options with preview java features enabled
    val COMPILER_OPTIONS =
        listOf("-Xlint:deprecation", "-Xlint:unchecked")

    withType<JavaCompile>() {
        options.compilerArgs = COMPILER_OPTIONS;
        options.encoding = "UTF8"
    }

    named<Test>("test") {
        // Use JUnit Platform for unit tests.
        useJUnitPlatform()
    }

    named<JavaExec>("run") {
        standardInput = System.`in`
    }
}
