## Overall Docker Setup for Coq's CI.

This directory provides Docker images to be used by Coq's CI. The
images do support Docker autobuild on `hub.docker.com` and Gitlab's
private registry.

The Gitlab CI will build a docker image unless the CI environment variable
`SKIP_DOCKER` is set to `true`. This image will be
stored in the [Gitlab container registry](https://gitlab.com/coq/coq/container_registry)
under the name given by the `CACHEKEY` variable from
the [Gitlab CI configuration file](../../../.gitlab-ci.yml).

In Coq's default CI, `SKIP_DOCKER` is set so as to avoid running a lengthy redundant job.

It can be used to regenerate a fresh Docker image on Gitlab through the following steps.
- Change the `CACHEKEY` variable to a fresh name in the CI configuration in a new commit.
- Push this commit to a Github PR. This will trigger a Gitlab CI run that will
  immediately fail, as the Docker image is missing and the `SKIP_DOCKER`
  default value prevents rebuilding the image.
- Run a new pipeline on Gitlab with that PR branch, using the green "Run pipeline"
  button on the [web interface](https://gitlab.com/coq/coq/pipelines),
  with the `SKIP_DOCKER` environment variable set to `false`. This will run a `docker-boot` process, and
  once completed, a new Docker image will be available in the container registry,
  with the name set in `CACHEKEY`.
- Any pipeline with the same `CACHEKEY` will now automatically reuse that
  image without rebuilding it from scratch.

For documentation purposes, we also require keeping in sync the `CACHEKEY` comment
from the first line of the [Dockerfile](bionic_coq/Dockerfile) in the same
commit.

In case you do not have the rights to run Gitlab CI pipelines, you should ask
the ci-maintainers Github team to do it for you.

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
