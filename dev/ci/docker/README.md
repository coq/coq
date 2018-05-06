## Overall Docker Setup for Coq's CI.

This directory provides Docker images to be used by Coq's CI. The
images do support Docker autobuild on `hub.docker.com`

Autobuild is the preferred build method [see below]; if you are a
member of the `coqci` organization, the automated build will push the
image to the `coqci/name:$VERSION` tag using a Docker hub hook.

## Updating the Image and Syncronization with CI files

Unfortunately, at this point some manual synchronization is needed
between the `Dockerfile` and `.gitlab-ci.yml`. In particular, the
checklist is:

- check the name and version of the image setup in `hooks/post_push`
  have to match.
- check `COMPILER` variables do match.

Once you are sure the variables are right, then proceed to trigger an
autobuild or do a manual build, et voilà !

## Docker Autobuilding.

We provide basic support for auto-building, see:

https://docs.docker.com/docker-cloud/builds/advanced/

If you are member of the `coqci` Docker organization, trigger an
autobuild in your account and the image will be pushed to it as we
set the proper tag in `hooks/post_push`.

We still need to figure out how properly setup a more automated,
organization-wide auto-building process.

## Manual Building

You can also manually build and push any image:

- Build the image `docker build -t base:$VERSION .`

To upload/push to your hub:

- Create a https://hub.docker.com account.
- Login into your space `docker login --username=$USER`
- Push the image:
  + `docker tag base:$VERSION $USER/base:$VERSION`
  + `docker push $USER/base:$VERSION`

Now your docker image is ready to be used. To upload to `coqci`:
- `docker tag base:$VERSION coqci/base:$VERSION`
- `docker push coqci/base:$VERSION`

## Debugging / Misc

To open a shell inside an image do `docker run -ti --entrypoint /bin/bash <imageID>`

Each `RUN` command creates an "layer", thus a Docker build is
incremental and it always help to put things updated more often at the
end.

## Possible Improvements:

- Use ARG for customizing versions, centralize variable setup;
- Learn more about Docker registry for GITLAB https://gitlab.com/coq/coq/container_registry .
