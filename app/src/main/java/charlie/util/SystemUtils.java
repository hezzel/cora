/**************************************************************************************************
 Copyright 2024--2025 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.util;

import java.util.Optional;

public class SystemUtils {

  public static enum SUPPORTED_OS { WINDOWS, LINUX, MAC }

  private static final String WIN_NAME_PREFIX = "Windows";

  private static final String OS_NAME    = System.getProperty("os.name");
  private static final String OS_VERSION = System.getProperty("os.version");

  static boolean checkOSName(String osName, String osNamePrefix) {
    if (osName == null || osName.isEmpty()) {
      return false;
    }
    return osName.startsWith(osNamePrefix);
  }

  static boolean checkOSVersion(String osVersion, String osVersionPrefix) {
    if (osVersion == null || osVersion.isEmpty()) {
      return false;
    }
    final String[] versionPrefixParts = osVersionPrefix.split("\\.");
    final String[] versionParts = osVersion.split("\\.");
    for (int i = 0; i < Math.min(versionPrefixParts.length, versionParts.length); i++) {
      if (!versionPrefixParts[i].equals(versionParts[i])) {
        return false;
      }
    }
    return true;
  }

  static boolean checkOS(String osName,
                         String osVersion,
                         String osNamePrefix,
                         String osVersionPrefix) {

    if (osName == null || osName.isEmpty() || osVersion == null || osVersion.isEmpty()) {
      return false;
    }
    return checkOSName(osName, osNamePrefix) && checkOSVersion(osNamePrefix, osVersionPrefix);
  }

  public static final boolean IS_OS_LINUX =
    checkOSName(OS_NAME, "Linux") || checkOSName(OS_NAME,"LINUX");

  public static final boolean IS_OS_MAC =
    checkOSName(OS_NAME, "Mac") || checkOSName(OS_NAME,"MAC");

  public static final boolean IS_OS_WINDOWS =
    checkOSName(OS_NAME, WIN_NAME_PREFIX + " 10") ||
      checkOSName(OS_NAME, WIN_NAME_PREFIX + " 11");

  public static boolean IS_UNIX_LIKE = IS_OS_LINUX || IS_OS_MAC;

  public static boolean isOSSupported() {
    return IS_OS_LINUX || IS_OS_MAC || IS_OS_WINDOWS;
  }

  public static Optional<SUPPORTED_OS> getCurrentOS() {
    if (IS_OS_LINUX)    { return Optional.of(SUPPORTED_OS.LINUX);   }
    if (IS_OS_MAC)      { return Optional.of(SUPPORTED_OS.MAC);     }
    if (IS_OS_WINDOWS)  { return Optional.of(SUPPORTED_OS.WINDOWS); }
    return Optional.empty();
  }

}
