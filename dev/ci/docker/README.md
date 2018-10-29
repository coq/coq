## Overall Docker Setup for Coq's CI.

This directory provides Docker images to be used by Coq's CI. The
images do support Docker autobuild on `hub.docker.com` and Gitlab's
private registry.

## Manual Building

You can also manually build and push any image:

- Build the image `docker build -t base:$VERSION .`

To upload/push to your hub:

- Create a https://hub.docker.com account.
- Login into your space `docker login --username=$USER`
- Push the image:
  + `docker tag base:$VERSION $USER/base:$VERSION`
  + `docker push $USER/base:$VERSION`

## Debugging / Misc

To open a shell inside an image do `docker run -ti --entrypoint /bin/bash <imageID>`

Each `RUN` command creates an "layer", thus a Docker build is
incremental and it always help to put things updated more often at the
end.

## Possible Improvements:

- Use ARG for customizing versions, centralize variable setup;
