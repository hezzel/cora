package cora.rwinduction.engine;

class CommandParser {

  static String[] split(String command) {

    return command.trim().split("\\s+");

  }

  static int parseIndex(String command) throws NumberFormatException {

    return Integer.parseInt(command);
  }

}
