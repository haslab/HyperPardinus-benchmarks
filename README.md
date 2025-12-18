# Alloy + HyperPardinus

We have prepared a docker container to make it easier to test the Alloy Analyzer with support for HyperPardinus.

## Benchmarks

There are containers for `arm64` and for `amd64`. The correct one is chosen automatically, otherwise use `--platform=<platform>`.

Run in interactive mode:

```
sudo docker run -it hyperalloy/hyperalloy /bin/bash
```

Inside the container, just move into the `benchmarks` folder:

```
cd benchmarks
```

Then, to reproduce either our low-level benchmarks or our high-level benchmarks, run one of the following:

```
./benchs.py doLow
./benchs.py doHigh
```

Any arising errors are written to the `logs` folder.

## GUI

To experiment with the GUI, you will have to setup a X server in your host machine, which will depend on your host OS.
First make sure that you have a X server running, and set the `DISPLAY` env variable accordingly.

### On Mac

1. Install the XQuartz X server.
2. Go to `XQuartz > Preferences > Security` and check `Allow connections from network clients`.
3. Launch the X11 server with `xhost +`.
4. Set the `DISPLAY` variable with `export DISPLAY=host.docker.internal:0`.

### Launching the GUI

To launch the GUI, just run the container, which will call the Alloy Analyzer by default:

```
sudo docker run --net=host --env="DISPLAY" -it hyperalloy/hyperalloy
```