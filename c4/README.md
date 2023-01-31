# The C4 Model

This directory is a collection of [C4 model](https://c4model.com/) diagrams for visualizing the architecture of various aspects of the Midnight system. Each subdirectory is dedicated to a view of the system:

- `dapp` - diagrams for decentralized applications built against Midnight

The directory structure of the system aspect being modeled should be `$ASPECT/$TYPE` where `$ASPECT` is that which is being modeled and `$TYPE` is the type of C4 diagram, either system context, container, component, or code. Within each `$TYPE` directory, images and UML source code should be separated into `images` and `uml` directories. The diagrams should be created using the [C4-PlantUML](https://github.com/plantuml-stdlib/C4-PlantUML) library to have consistent formatting.