package cora.rwinduction.engine;

import charlie.util.either.Either;

interface Command extends RunnableArguments {

  Either<String, Boolean> run(String args);

}
