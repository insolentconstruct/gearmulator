cmake_minimum_required(VERSION 3.10)

project(xmemProbe)

add_executable(xmemProbe)

set(SOURCES
	xmemProbe.cpp
)

target_sources(xmemProbe PRIVATE ${SOURCES})
source_group("source" FILES ${SOURCES})

target_link_libraries(xmemProbe PUBLIC virusConsoleLib)

if(UNIX AND NOT APPLE)
	target_link_libraries(xmemProbe PUBLIC -static-libgcc -static-libstdc++)
endif()

set_property(TARGET xmemProbe PROPERTY FOLDER "Virus")
