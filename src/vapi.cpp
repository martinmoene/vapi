// Copyright 2015 by Martin Moene
//
// vapi ... .
//
// This code is licensed under the MIT License (MIT).
//

// VHDL
// - Hyperlinked VHDL-93 BNF Syntax
//   https://tams.informatik.uni-hamburg.de/vhdl/tools/grammar/vhdl93-bnf.html
// - vbd - a script for generating ASCII block diagrams from VHDL entity descriptions
//   http://p-code.org/vbd.html

// Spirit
// - http://stackoverflow.com/questions/12217515/resolve-ambiguous-boostspiritqi-grammar-with-lookahead
// - http://boost-spirit.com/home/wp-content/uploads/2010/05/spirit_presentation.pdf
// - Tracking the Input Position While Parsing, 
//   http://boost-spirit.com/home/articles/qi-example/tracking-the-input-position-while-parsing/
//   (http://stackoverflow.com/a/10661880)

// Ideas
// - skipping upto entity
// - data structure for parsing and generation (try out in vgen.cpp))
// - Commandline options (files, output format, )
// - Error reporting with line number and caret position


#include <boost/config/warning_disable.hpp>
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/karma.hpp>
#include <boost/spirit/include/phoenix.hpp>
#include <boost/spirit/include/support_line_pos_iterator.hpp>
#include <boost/fusion/include/adapted.hpp>
//#include <boost/fusion/include/adapt_struct.hpp>

#include <iomanip>
#include <iostream>
#include <string>
#include <vector>

#ifndef  vapi_REPORT_LINENO
# define vapi_REPORT_LINENO  1
#endif

#ifndef  vapi_DEBUG_PARSER
# define vapi_DEBUG_PARSER  0
#endif

namespace client
{
    namespace qi  = boost::spirit::qi;
    namespace phx = boost::phoenix;

    typedef std::string text;
    typedef std::vector< text > texts;

    struct signal_t
    {
        texts names;
        text direction;
        text type;
    };

    typedef std::vector< signal_t > signals_t;

    struct entity_t  
    {
        text name;
        signals_t signals;
    };

    typedef std::vector< entity_t > entities_t;
}

// Global namespace
BOOST_FUSION_ADAPT_STRUCT(
    client::signal_t,
    (client::texts, names)
    (client::text , direction)
    (client::text , type)
)

BOOST_FUSION_ADAPT_STRUCT(
    client::entity_t,
    (client::text     , name)
    (client::signals_t, signals)
)
    
namespace client
{
//    typedef signal_t  element_t;
//    typedef entity_t  data_t;
    typedef std::string  element_t;
    typedef std::vector< element_t > data_t;
    
    struct location 
    { 
        int line, column; 
        location( int line, int column ) 
            : line( line ), column( column )  {} 
    };

    inline std::ostream & operator<<( std::ostream & os, location where )
    {
#ifdef __GNUG__
        return os << ":" << where.line << ":" << where.column;
#else
        return os << "(" << where.line << "." << where.column << ")";
#endif
    }

    template <typename Iterator>
    struct error_handler
    {
        std::string file;

        error_handler( std::string file )
            : file( file ) {}

        void operator()
        (
            Iterator first, Iterator last,
            Iterator err_pos, boost::spirit::info const & what ) const
        {
            auto const tabsize = 8;
            auto const lineno  = get_line( err_pos );
            auto const start   = get_line_start( first, err_pos );
            auto const column  = get_column( start, err_pos, tabsize );
            auto const text    = get_current_line( start, err_pos, last );
            
            std::cerr 
#if vapi_REPORT_LINENO            
                << "vapi: "<< file << location( lineno, column ) << ": expected " << what << "\n"
#else
                << "vapi: "<< file << ": expected " << what << "\n"
#endif
                << strip( text.begin(), text.end() ) << "\n"
                << std::setw( column ) << " " << "^~~~\n" ;
        }
        
        // get_current_line() yields thecurrent line /and/ all following lines;
        // here we strip the trailing lines.
        
        template< typename Iterator_ >
        static std::string strip( Iterator_ first, Iterator_ last )
        {
            std::string text( first, last );
            
            if ( 0 == text.find('\n') )
                text = text.substr( 1 );
            
            auto pos = text.find('\n');
            if ( std::string::npos != pos )
                text = text.substr( 0, pos );

            return text; 
        }
    };

    template< typename Iterator >
    struct vhdl_skipper : qi::grammar<Iterator>
    {
        vhdl_skipper() : vhdl_skipper::base_type( start, "vhdl-skipper" )
        {
            using qi::eol;
            using qi::lit;
            using qi::char_;
            using qi::space;

            // skip whitespace, comment
            start = space 
                |   lit("--") >> *(char_ - eol) 
                ;
        }

        qi::rule<Iterator> start;
    };

    template< typename Iterator, typename  Skipper >
    struct vhdl_grammar : qi::grammar<Iterator, data_t(), Skipper>
    {
        vhdl_grammar( std::string file ) 
            : vhdl_grammar::base_type( start, "VHDL(entity)" )
        {
            using qi::int_;
            using qi::char_;
            using qi::lit;
            using qi::lexeme;
            using qi::no_case;
            using qi::omit;

            start %= 
                *( entity )                         ;
                
            skip = 
                ( omit[ *( !lit("entity") >> entity_) ] )      ;

            entity %=
                entity_ > identifier > is_          > 
                    entity_header                   >
//                  entity_declarative_part         >
                -( begin_                           >
                    entity_statement_part )         >
                end_ > -( entity_) > -( entity_simple_name ) > ';' ;

            entity_header %= 
//              -( generic_clause )                 >>
                -( port_clause )                    ;

            port_clause %=
                port_ > '(' > port_list > ')' > ';' ;

            port_list %= 
                interface_list                      ;

            interface_list %=
                interface_element % ';'             ;

            interface_element %= 
                interface_declaration ;

            interface_declaration %=
//              interface_constant_declaration
                  interface_signal_declaration
//              | interface_signal_declaration
//              | interface_variable_declaration
//              | interface_file_declaration
                ;

            interface_signal_declaration %=
                -( signal_) > identifier_list > ':' > -( mode ) > subtype_indication > -(bus_) > -( lit(":=") > /*static_*/expression ) ;

            identifier_list %= 
                identifier % ',' ;

            subtype_indication %=
                /*-( resolution_function_name ) >>*/ type_mark > -( constraint ) ;

            type_mark %=
                identifier ;    // simplification
//                type_name
//                | subtype_name ;

            constraint %= 
                '(' > expression > direction > expression > ')'; // simplification

            expression %=
                int_ ;
//                  relation { AND relation }
//                | relation { OR relation }
//                | relation { XOR relation }
//                | relation [ NAND relation ]
//                | relation [ NOR relation ]
//                | relation { XNOR relation }

            entity_statement_part = identifier; // TMP
            entity_simple_name = identifier;
            
//            identifier %= ((char_("a-zA-Z_") >> *char_("a-zA-Z_0-9")) );
            identifier = ((char_("a-zA-Z_") >> *char_("a-zA-Z_0-9")) - keyword );
            
            keyword    = ( entity_ | is_ | port_ | begin_ | end_ | mode | direction );
            mode       = ( inout_ | in_ | out_ | buffer_ | linkage_ );
            direction  = ( to_ | downto_ );

            // sorted alphabetically from long to short to match longest first:
            to_        = no_case[ lexeme["to"] ];
            signal_    = no_case[ lexeme["signal"] ];
            port_      = no_case[ lexeme["port"] ];
            out_       = no_case[ lexeme["out"] ];
            linkage_   = no_case[ lexeme["linkage"] ];
            is_        = no_case[ lexeme["is"] ];
            inout_     = no_case[ lexeme["inout"] ];
            in_        = no_case[ lexeme["in"] ];
            entity_    = no_case[ lexeme["entity"] ];
            end_       = no_case[ lexeme["end"] ];
            downto_    = no_case[ lexeme["downto"] ];
            bus_       = no_case[ lexeme["bus"] ];
            buffer_    = no_case[ lexeme["buffer"] ];
            begin_     = no_case[ lexeme["begin"] ];

            start                .name("start");

            skip                 .name("skip");
            entity               .name("entity");
            entity_header        .name("entity-header");
            port_clause          .name("port-clause");
            port_list            .name("port-list");
            interface_list       .name("interface-list");
            interface_element    .name("interface-element");
            interface_declaration.name("interface-declaration");
            interface_signal_declaration.name("interface-signal-declaration");
            identifier_list      .name("identifier-list");
            subtype_indication   .name("subtype");
            type_mark            .name("type");
            constraint           .name("constraint");
            
            entity_simple_name   .name("simple-name");
            entity_statement_part.name("statement");

            expression.name("expression");
            identifier.name("identifier");        
            keyword   .name("keyword");
            mode      .name("mode");
            direction .name("direction");

            entity_   .name("entity_");
            is_       .name("is");
            port_     .name("port");
            begin_    .name("begin");
            end_      .name("end");
            signal_   .name("signal");
            bus_      .name("bus");
            in_       .name("in");
            out_      .name("out");
            inout_    .name("inout");
            buffer_   .name("buffer");
            linkage_  .name("linkage");
            to_       .name("to");
            downto_   .name("downto");

#if vapi_DEBUG_PARSER
            qi::debug( start );
            qi::debug( skip );
            qi::debug( entity );
            qi::debug( mode );
            qi::debug( direction );
            qi::debug( keyword );
            qi::debug( identifier );
            qi::debug( constraint  );

            qi::debug( lp_ );
            qi::debug( rp_ );

            qi::debug( entity_ );
            qi::debug( is_ );
            qi::debug( port_ );
            qi::debug( begin_ );
            qi::debug( end_ );
            qi::debug( signal_ );
            qi::debug( bus_ );
            qi::debug( in_ );
            qi::debug( out_ );
            qi::debug( inout_ );
#endif
            // install error handler:
            
            using qi::_1;
            using qi::_2;
            using qi::_3;
            using qi::_4;

            phx::function< error_handler<Iterator> > const handler( error_handler<Iterator>( file.c_str() ) );
            qi::on_error<qi::fail>( start, handler(_1, _2, _3, _4) );
        }

        // parser rules:
        
        qi::rule<Iterator, data_t(), Skipper> start;

        qi::rule<Iterator, Skipper> skip;
        qi::rule<Iterator, element_t(), Skipper> entity;
        qi::rule<Iterator, element_t(), Skipper> entity_header;
        qi::rule<Iterator, element_t(), Skipper> port_clause;
        qi::rule<Iterator, element_t(), Skipper> port_list;
        qi::rule<Iterator, element_t(), Skipper> interface_list;
        qi::rule<Iterator, element_t(), Skipper> interface_element;
        qi::rule<Iterator, element_t(), Skipper> interface_declaration;
        qi::rule<Iterator, element_t(), Skipper> interface_signal_declaration;
        qi::rule<Iterator, element_t(), Skipper> identifier_list;
        qi::rule<Iterator, element_t(), Skipper> subtype_indication;
        qi::rule<Iterator, element_t(), Skipper> type_mark;
        qi::rule<Iterator, element_t(), Skipper> constraint;
        
        qi::rule<Iterator, element_t(), Skipper> entity_simple_name;
        qi::rule<Iterator, element_t(), Skipper> entity_statement_part;

        qi::rule<Iterator, element_t(), Skipper> expression;
        qi::rule<Iterator, element_t()> identifier;     
        qi::rule<Iterator, element_t()> keyword;
        qi::rule<Iterator, element_t()> mode;
        qi::rule<Iterator, element_t()> direction;

        qi::rule<Iterator> entity_ ;
        qi::rule<Iterator> is_;
        qi::rule<Iterator> port_;
        qi::rule<Iterator> begin_ ;
        qi::rule<Iterator> end_ ;
        qi::rule<Iterator> signal_;
        qi::rule<Iterator> bus_ ;
        qi::rule<Iterator> in_;
        qi::rule<Iterator> out_;
        qi::rule<Iterator> inout_ ;
        qi::rule<Iterator> buffer_;
        qi::rule<Iterator> linkage_;
        qi::rule<Iterator> to_;
        qi::rule<Iterator> downto_;
    };

    // parse the VHDL content of a single file:

    template< typename Iterator, typename Data >
    bool parse_vhdl( std::string file, Iterator first, Iterator last, Data & data )
    {
        using qi::phrase_parse;

        typedef vhdl_skipper<Iterator> vhdl_skipper;
        typedef vhdl_grammar<Iterator, vhdl_skipper> vhdl_parser;

        try
        {
            vhdl_skipper skipper;
            vhdl_parser  parser( file );
        
            bool result = phrase_parse(
                first     // start iterator
                , last    // end iterator
                , parser  // the parser
                , skipper // the skip-parser
                , data    // the collected data
            );
            
            if ( first != last ) 
            {
//                std::cerr << "vapi: trailing unparsed: '" << std::string( first, last ) << "'\n";
            }
            
            // fail if we did not get a full match:
            return ( first != last ) ? false: result;
        }
        catch( qi::expectation_failure<Iterator> const & e )
        {
            std::string fragment( e.first, e.last );
            std::cerr << "vapi: " << "line:" << get_line(e.first) << "\n";
            std::cerr << "vapi: " << e.what() << "'" << fragment << "'\n";
        }

        return false;   // error
    }
}

#include <fstream>

int main( int argc, char * argv[] )
{
    std::string path = "input.txt";
    
    if ( argc > 1 )
        path = argv[1];
        
    std::ifstream ifs( path.c_str() /*, std::ios::binary*/);
    ifs.unsetf( std::ios::skipws );


#if vapi_REPORT_LINENO
    // https://gist.github.com/sehe/1425972
    
    typedef std::string::const_iterator raw_it_t;
    typedef boost::spirit::line_pos_iterator<raw_it_t> line_pos_iterator;

    std::string buffer( std::istreambuf_iterator<char>( ifs ), ( std::istreambuf_iterator<char>() ) );
    line_pos_iterator first( buffer.begin() ), last( buffer.end() );
#else
    boost::spirit::istream_iterator first( ifs ), last;
#endif

    client::data_t data;

    if ( ! client::parse_vhdl( path, first, last, data ) )
    {
        std::cout << "failed" << "\n";
        return EXIT_FAILURE;
    }
    std::cout << "passed" << "\n";

//    for ( auto & text : data )
//    {
//        std::cout << "data: " << text << '\n';
//    }

    namespace karma = boost::spirit::karma;
    
    std::cout << karma::format( karma::string % ", ", data ) << "\n";

    return EXIT_SUCCESS;
}

#if 0
entity abc is port( a : in b ); end entity xyz;
entity abc is port( a : in b ); end entity xyz; -- comment
entity abc is port( a : in b bus := 42 ); end entity xyz; -- comment

g++                  -I"D:\My Documents\00_IP\SpmDev\Vendor\boost_1_57_0" -o vapi.exe ../src/vapi.cpp && vapi.exe
g++ -Wall -std=c++11 -I"D:\My Documents\00_IP\SpmDev\Vendor\boost_1_57_0" -o vapi.exe ../src/vapi.cpp && vapi.exe
g++ -Wall -std=c++11 -I"D:\Own\Martin\Work\Client\IP\Project\Camera\Vendor\boost_1_59_0" -o vapi.exe ../src/vapi.cpp && vapi.exe
g++                  -I"D:\Own\Martin\Work\Client\IP\Project\Camera\Vendor\boost_1_59_0" -o vapi.exe ../src/vapi.cpp && vapi.exe < input.txt

cl -W3 -EHsc         -I"D:\My Documents\00_IP\SpmDev\Vendor\boost_1_57_0"  vapi.cpp && ../src/vapi.exe < input.txt
cl -W3 -EHsc         -I"D:\Own\Martin\Work\Client\IP\Project\Camera\Vendor\boost_1_59_0" ../src/vapi.cpp && vapi.exe < input.txt
#endif

// end of file
