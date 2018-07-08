configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)
set(indra_public_headers "")

add_library(libindra
    anf.cpp
    cnf.cpp
    karnaugh.cpp
    satsolve.cpp
    simplifybysat.cpp
    replacer.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
)
target_link_libraries(libindra
    ${M4RI_LIBRARIES}
)

install(TARGETS libindra
    EXPORT ${indra_EXPORT_NAME}
    LIBRARY DESTINATION "${CMAKE_INSTALL_PREFIX}/lib"
    ARCHIVE DESTINATION "${CMAKE_INSTALL_PREFIX}/lib"
    PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_PREFIX}/include/indra"
)

###############

add_executable(indra
    main.cpp
)
set_target_properties(indra PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR})
set_target_properties(indra PROPERTIES INSTALL_RPATH_USE_LINK_PATH TRUE)

if (STATICCOMPILE)
    SET_TARGET_PROPERTIES(indra PROPERTIES LINK_SEARCH_START_STATIC 1)
endif()

target_link_libraries(indra
    libindra
    MV
    ${Boost_LIBRARIES}
    ${PNG_LIBRARIES}
    ${M4RI_LIBRARIES}
    polybori
    ${CRYPTOMINISAT5_LIBRARIES}
)
install(TARGETS indra
    EXPORT ${indra_EXPORT_NAME}
    RUNTIME DESTINATION bin
)

SET(CPACK_PACKAGE_EXECUTABLES "indra")
