configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)
set(anfconv_public_headers "")

add_library(libanfconv
    anf.cpp
    cnf.cpp
    karnaugh.cpp
    satsolve.cpp
    simplifybysat.cpp
    iterativeSolver.cpp
    replacer.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
)
target_link_libraries(libanfconv
    ${M4RI_LIBRARIES}
)

install(TARGETS libanfconv
    EXPORT ${ANFCONV_EXPORT_NAME}
    LIBRARY DESTINATION "${CMAKE_INSTALL_PREFIX}/lib"
    ARCHIVE DESTINATION "${CMAKE_INSTALL_PREFIX}/lib"
    PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_PREFIX}/include/anfconv"
)

###############

add_executable(anfconv
    main.cpp
)
set_target_properties(anfconv PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR})
set_target_properties(anfconv PROPERTIES INSTALL_RPATH_USE_LINK_PATH TRUE)

if (STATICCOMPILE)
    SET_TARGET_PROPERTIES(anfconv PROPERTIES LINK_SEARCH_START_STATIC 1)
endif()

target_link_libraries(anfconv
    libanfconv
    MV
    ${Boost_LIBRARIES}
    ${PNG_LIBRARIES}
    ${M4RI_LIBRARIES}
    polybori
    ${CRYPTOMINISAT5_LIBRARIES}
)
install(TARGETS anfconv
    EXPORT ${ANFCONV_EXPORT_NAME}
    RUNTIME DESTINATION bin
)

SET(CPACK_PACKAGE_EXECUTABLES "anfconv")
