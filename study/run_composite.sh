#!/bin/bash
java -Xss15M -jar target/scala-2.12/gvc0-assembly-0.1.0-SNAPSHOT.jar -b ./study/benchmarks/composite/ --only-exec -ws 2 -wu 32 -i 7 ./src/test/resources/quant-study/composite.c0; shutdown -h now