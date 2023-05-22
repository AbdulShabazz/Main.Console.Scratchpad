#include <iostream>
#include <string>
#include <chrono>
//#include <Euclid.TestCase.246.h>
#include <Euclid.16.Boost.Support.No.Strings.h>

int main()
{
    Euclid_Prover::__stdtracein__("Main");

    const auto start_time_chrono = std::chrono::high_resolution_clock::now();

    std::cout << "Working..." << std::endl;

    Euclid_Prover::Prove();

    std::cout << std::endl;
    const auto end_time_chrono = std::chrono::high_resolution_clock::now();
    const auto duration_chrono = std::chrono::duration_cast<std::chrono::nanoseconds>( end_time_chrono - start_time_chrono ).count();
    std::cout << "Total Duration (nanoseconds): " << duration_chrono << std::endl;

    Euclid_Prover::__stdtraceout__("Main");

    std::string Hold_for_user_input{};
    std::cin >> Hold_for_user_input;

    return EXIT_SUCCESS;
}
