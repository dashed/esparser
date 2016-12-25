use ::CurrentPosition;

error_chain! {

    errors {
        ParseError(loc: CurrentPosition, descr: String) {
            description(descr)
            display("Line {}, Column {}: {}", loc.line(), loc.col(), descr)
        }
    }

    // foreign_links {
    //     // ChompError(::FooError);

    //     // ChompError(Foo);
    // }

    // #[derive(Debug)]
    // pub enum ParseError {
    //     Expected(loc: CurrentPosition, descr: String) {
    //         description(descr)
    //         display("Line {}, Column {}: {}", loc.line(), loc.col(), descr)
    //     }
    //     Error {
    //         // TODO: fix
    //         description("Error with no description occured")
    //     }
    // }
}
