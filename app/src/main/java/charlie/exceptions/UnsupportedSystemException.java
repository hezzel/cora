package charlie.exceptions;

public class UnsupportedSystemException extends RuntimeException {
  public UnsupportedSystemException() {
    super("Unsupported operating system: " + System.getProperty("os.name"));
  }
}
