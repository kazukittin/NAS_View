plugins {
    id("com.android.application")
}

android {
    namespace = "com.example.nasview"
    compileSdk = 35

    defaultConfig {
        applicationId = "com.example.nasview"
        minSdk = 26
        targetSdk = 35
        versionCode = 1
        versionName = "0.1.0"
    }
}

dependencies {
    implementation("com.hierynomus:smbj:0.13.0")
    implementation("eu.agno3.jcifs:jcifs-ng:2.1.10")
}
