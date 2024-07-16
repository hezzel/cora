package charlie.exceptions;

public class UnsupportedSystemException extends RuntimeException {
  public UnsupportedSystemException() {
    String osName = System.getProperty("os.name");
    super("Unsupported operating system: " + osName);
  }
}
