module gamma.runtime.Scanner;

public interface Scanner
{
    enum EOF = -1;

    int nextToken();

    int line();

    int column();
}
