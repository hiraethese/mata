// TODO: some header

#include "../3rdparty/catch.hpp"

#include <vata2/vm.hh>

using namespace Vata2::Parser;
using namespace Vata2::VM;

TEST_CASE("Vata2::VM::VirtualMachine::run_code() correct calls")
{
	// setting the environment
	VirtualMachine mach;
	ParsedSection sec;
	sec.type = "CODE";

	SECTION("empty program")
	{
		mach.run_code(sec);
	}

	SECTION("Hello World")
	{
		sec.body.push_back({"(", "print", "Hello World!", ")"});

		// we wish to catch output
		std::ostringstream cout_buf;
		std::streambuf* old_cout = std::cout.rdbuf(cout_buf.rdbuf());

		mach.run_code(sec);

		std::cout.rdbuf(old_cout);

		REQUIRE((cout_buf.str() == "Hello World!"));
	}

	SECTION("aux")
	{
		WARN_PRINT("Insufficient testing of Vata2::VM::VirtualMachine::run_code()");
	}

}

TEST_CASE("Vata2::VM::VirtualMachine::run_code() invalid calls")
{
	// setting the environment
	VirtualMachine mach;
	ParsedSection sec;
	sec.type = "CODE";

	SECTION("incorrectly formed code 1")
	{
		sec.body.push_back({"(", ")"});
		CHECK_THROWS_WITH(mach.run_code(sec),
			Catch::Contains("is not a valid function call"));
	}

	SECTION("incorrectly formed code 2")
	{
		sec.body.push_back({"(", "(", "return", "a", ")", ")"});
		CHECK_THROWS_WITH(mach.run_code(sec),
			Catch::Contains("is not a valid function call"));
	}

	SECTION("incorrectly formed code 3")
	{
		sec.body.push_back({"(", "load_aut", ")"});
		CHECK_THROWS_WITH(mach.run_code(sec),
			Catch::Contains("is not a valid function call"));
	}

	SECTION("aux")
	{
		WARN_PRINT("Insufficient testing of Vata2::VM::VirtualMachine::run_code()");
	}
}

TEST_CASE("Vata2::VM::VirtualMachine::default_dispatch() calls")
{
	// setting the environment
	VirtualMachine mach;
	ParsedSection sec;
	sec.type = "CODE";

	SECTION("return with more than 1 argument")
	{
		sec.body.push_back({"(", "return", "arg1", "args2", ")"});
		CHECK_THROWS_WITH(mach.run_code(sec),
			Catch::Contains("requires 1 argument"));
	}

	SECTION("invalid function name")
	{
		sec.body.push_back({"(", "invalid_func_name", "arg1", ")"});
		CHECK_THROWS_WITH(mach.run_code(sec),
			Catch::Contains("is not a defined function"));
	}

	SECTION("aux")
	{
		WARN_PRINT("Insufficient testing of Vata2::VM::VirtualMachine::run_code()");
	}
}
