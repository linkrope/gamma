module gamma.util.Position;

public import io : Position;


public void markError(Position position, string message)
{
    import log : error;

    error!"%s\n%s"(message, position);
}
