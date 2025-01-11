## Overall Docker Setup for Rocq's CI.

This directory provides Docker images to be used by Rocq's CI. The
images do support Docker autobuild on `hub.docker.com` and Gitlab's
private registry.

The Gitlab CI will build a Docker image unless the CI environment variable
`SKIP_DOCKER` is set to `true`. This image will be
stored in the [Gitlab container registry](https://gitlab.com/coq/coq/container_registry)
under the name given by the `CACHEKEY` variable from
the [Gitlab CI configuration file](../../../.gitlab-ci.yml).

`SKIP_DOCKER` is set to "true" in `https://gitlab.com/coq/coq` to avoid running
a lengthy redundant job.  For efficiency, users should enable that setting
in forked repositories after the initial Docker build in the fork succeeds.

The steps to generate a new Docker image are:
- Update the `CACHEKEY` variable in .gitlab-ci.yml with the date and md5.
- Submit the change in a PR. coqbot will detect that the Dockerfile
  has changed and will trigger a pipeline build with `SKIP_DOCKER` set
  to `false`. This will run a `docker-boot` process, and once
  completed, a new Docker image will be available in the container
  registry, with the name set in `CACHEKEY`.
- Any pipeline with the same `CACHEKEY` will now automatically reuse that
  image without rebuilding it from scratch.

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
