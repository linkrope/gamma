module gamma.runtime.Lexer;

import io : Position;

public interface Lexer
{
    int nextToken();

    Position position();
}
