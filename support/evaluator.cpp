#include <vector>
#include <iostream>
#include <fstream>
#include <sstream>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <sys/time.h>
using namespace std;

#define TIMEOUT "60"

typedef vector<string> stringlist;
typedef vector<int> intlist;

vector<string> files;
vector<string> setup_names;
vector<string> setup_args;
vector<string> query_names;
vector<string> query_args;
vector<stringlist> test_results;
vector<stringlist> test_result_files;
vector<intlist> test_times;
vector<intlist> query_results;
string title;
string header;
string footer;

/* ==================== basic functions ==================== */

void execute(string cmd) {
  system(cmd.c_str());
}

string remove_extension(string filename) {
  int k = filename.find_last_of('.');
  if (k == string::npos) return filename;
  else return filename.substr(0,k);
}

string get_basename(string filename) {
  int k = filename.find_last_of('/');
  if (k == string::npos) return filename;
  else return filename.substr(k+1);
}

string str(int i) {
  stringstream out;
  out << i;
  return out.str();
}

string print_time(int t) {
  string ret = str(t / 100) + ".";
  t %= 100;
  if (t < 10) ret += "0";
  ret += str(t);
  return ret;
}

string lower_case(string s) {
  for (int i = 0; i < s.length(); i++) {
    if (s[i] >= 'A' && s[i] <= 'Z') s[i] += 'a' - 'A';
  }
  return s;
}

/* ==================== run tests and queries ====================*/

string run_test(string filename, string settings, string outpfile,
                int &time_spent) {
  struct timeval starttime, endtime;

  // run wanda with the given settings
  gettimeofday(&starttime, NULL);
  cout << "running ./bin/app " << settings << " " << filename
       << " ... ";
  cout.flush();
  execute("timeout " TIMEOUT " ./bin/app " + settings + " " +
          filename + " > evaluator.tmp");
  cout << " done" << endl;
  gettimeofday(&endtime, NULL);

  // read the generated file
  ifstream inp("evaluator.tmp");
  string answer = "", txt = "";
  while (!inp.eof()) {
    string line;
    getline(inp, line);
    if (answer == "") answer = line;
    else txt += line + "\n";
  }
  inp.close();
  execute("rm evaluator.tmp");

  // print output file
  if (outpfile != "") {
    outpfile = "evaluation/details/" + outpfile;
    ofstream outp(outpfile.c_str());
    outp << txt;
    outp.close();
  }

  // determine time spent
  time_spent = (endtime.tv_sec - starttime.tv_sec) * 100 +
               (endtime.tv_usec - starttime.tv_usec) / 10000;

  if (answer == "") return "TIMEOUT";
  else return answer;
}

/* ==================== making the page ==================== */

void htmlify_input_file(int number) {
  string filename = remove_extension(get_basename(files[number]));
  execute("cp " + files[number] + " evaluation/details/" + filename + ".txt");
}

void make_page() {
  int i, j;

  cout << "creating page ...";
  cout.flush();

  string page =
    "<html>\n"
    "  <head>\n"
    "    <title>" + title + "</title>\n"
    "    <style type=\"text/css\">\n"
    "    td {\n"
    "      width: 6em;\n"
    "      margin: 0pt;\n"
    "      padding: 0pt;\n"
    "      text-align: center;\n"
    "    }   \n"
    "    td.filename {\n"
    "      width: 25em;\n"
    "      border-bottom: thin solid #888;\n"
    "      text-align: left;\n"
    "    }   \n"
    "    td a { \n"
    "      width: 100%;\n"
    "      display: block;\n"
    "      padding-top: 0.5ex;\n"
    "      padding-bottom: 0.5ex;\n"
    "      text-decoration: none;\n"
    "      color: black;\n"
    "    }   \n"
    "    a.yes {\n"
    "      background-color: #0f0;\n"
    "    }   \n"
    "    a.no {\n"
    "      background-color: #f00;\n"
    "    }   \n"
    "    a.maybe {\n"
    "      background-color: #ff0;\n"
    "    }   \n"
    "    a.timeout {\n"
    "      background-color: #f80;\n"
    "    }   \n"
    "    td.filename a {\n"
    "      text-align: left;\n"
    "    }\n"
    "    p.footer {\n"
    "      margin-top: 1em;\n"
    "      font-size:0.875em;\n"
    "    }\n"
    "    </style>\n"
    "  </head>\n"
    "  <body>\n" + header +
    "    <table>\n"
    "      <tr>\n"
    "        <th>Filename</th>\n";

  for (i = 0; i < setup_names.size(); i++) {
    page += "        <th>" + setup_names[i] + "</th>\n";
  }
  for (i = 0; i < query_names.size(); i++) {
    page += "        <th>" + query_names[i] + "</th>\n";
  }
  page += "      </tr>\n";

  for (j = 0; j < files.size(); j++) {
    string filename = remove_extension(get_basename(files[j]));

    page += "      <tr>\n"
      "        <td class=\"filename\"><a href=\"details/" + filename +
      ".txt\">" + filename + "</a></td>\n";

    for (i = 0; i < setup_names.size(); i++) {
      string result = test_results[i][j];
      string time = print_time(test_times[i][j]);
      page += "        <td>";
      if (result == "YES" || result == "NO") {
        page += "<a class=\"" + lower_case(result) +
          "\" href=\"details/" + test_result_files[i][j] + "\">" +
          result + " " + time + "</a>";
      }
      else {
        page += "<a class=\"" + lower_case(result) + "\">" + result +
                "</a>";
      }
      page += "        </td>\n";
    }

    for (i = 0; i < query_names.size(); i++) {
      if (query_results[i][j] == 1) {
        page += "        <td>&#x2713;</td>\n";
      }
      else {
        page += "        <td>&nbsp;</td>\n";
      }
    }
    page += "      </tr>\n";
  }

  vector<int> total_yes;
  vector<int> total_no;
  vector<int> total_maybe;
  vector<int> total_timeout;
  vector<int> total_time;

  int num_setups = setup_names.size();

  for (i = 0; i < num_setups; i++) {
    total_yes.push_back(0);
    total_no.push_back(0);
    total_maybe.push_back(0);
    total_timeout.push_back(0);
    total_time.push_back(0);
    for (j = 0; j < files.size(); j++) {
      if (test_results[i][j] == "YES") total_yes[i]++;
      if (test_results[i][j] == "NO") total_no[i]++;
      if (test_results[i][j] == "MAYBE") total_maybe[i]++;
      if (test_results[i][j] == "TIMEOUT") total_timeout[i]++;
      if (test_results[i][j] == "YES" || test_results[i][j] == "NO")
        total_time[i] += test_times[i][j];
    }
  }

  page += "      <tr>\n"
          "        <td><b>Total YES</b></td>\n";
  for (i = 0; i < num_setups; i++)
    page += "        <td>" + str(total_yes[i]) + "</td>\n";
  page += "      </tr>\n"
          "      <tr>\n        <td><b>Total NO</b></td>\n";
  for (i = 0; i < num_setups; i++)
    page += "        <td>" + str(total_no[i]) + "</td>\n";
  page += "      </tr>\n"
          "      <tr>\n        <td><b>Total MAYBE</b></td>\n";
  for (i = 0; i < num_setups; i++)
    page += "        <td>" + str(total_maybe[i]) + "</td>\n";
  page += "      </tr>\n"
          "      <tr>\n        <td><b>Total TIMEOUT</b></td>\n";
  for (i = 0; i < num_setups; i++)
    page += "        <td>" + str(total_timeout[i]) + "</td>\n";
  page += "      </tr>\n"
          "      <tr>\n        <td><b>Average Runtime</b></td>\n";
  for (i = 0; i < num_setups; i++) {
    int count = total_yes[i] + total_no[i];
    if (count == 0) page += "        <td>NA</td>\n";
    else page += "        <td>" + print_time(total_time[i]/count) +
                 "</td>\n";
  }

  page +=
    "    </table>\n" + footer +
    "  </body>\n"
    "</html>\n";

  ofstream pagefile("evaluation/page.html");
  pagefile << page;
  pagefile.close();

  cout << "done." << endl;
}

/* ==================== reading the setup ==================== */

bool read_setup() {
  int stage = 0;
  int k;
  string name, args;

  ifstream fin("evaluator.in");
  while (true) {
    string input;
    getline(fin, input);
    if (input == "") {
      if (stage < 4) {
        stage++;
        continue;
      }
      else break;
    }

    if (stage < 2) {
      k = input.find(':');
      if (k == string::npos) {
        cout << "error reading evaluator.in: could not parse ["
             << input << "]." << endl;
        fin.close();
        return false;
      }
      name = input.substr(0,k-1);
      args = input.substr(k+1);
    }

    if (stage == 0) {       // reading setup
      setup_names.push_back(name);
      setup_args.push_back(args);
    }
    else if (stage == 1) {  // reading queries
      query_names.push_back(name);
      query_args.push_back(args);
    }
    else if (stage == 2) {  // reading title
      title = input;
    }
    else if (stage == 3) {  // reading header
      header += input + "\n";
    }
    else if (stage == 4) {  // reading footer
      footer += input + "\n";
    }
  }

  fin.close();

  if (setup_names.size() == 0 && query_names.size() == 0) {
    cout << "error reading evaluator.in: file is empty!" << endl;
    return false;
  }

  return true;
}

void add_directory_contents(string dirname) {
  DIR *dir;
  struct dirent *ent;
  if ((dir = opendir(dirname.c_str())) != NULL) {
    /* print all the files and directories within directory */
    while ((ent = readdir(dir)) != NULL) {
      string fullname = dirname + ent->d_name;
      if (ent->d_name[0] == 0 || ent->d_name[0] == '.') continue;
      if (ent->d_type == DT_DIR)
        add_directory_contents(fullname + "/");
      else files.push_back(fullname);
    }
    closedir (dir);
  } else {
    /* could not open directory */
    perror ("");
    //return EXIT_FAILURE;
  }
}

int main(int argc, char **argv) {
  int i, j;

  if (argc == 1) {
    cout << "Welcome, earthling!" << endl << endl;
    cout << "EVALUATOR uses an input file evaluator.in; this file "
         << "should have the following format:" << endl << endl;
    cout << "First, a number of entries a : b, where a is the title "
         << "which you would like to appear in the table generated "
         << "by EVALUATOR, and b are the runtime arguments to send "
         << "to CORA.  Each of these entries should be on a "
         << "separate line." << endl << endl;
    cout << "Then, a number of entries of the form title : query, "
         << "where title is the title you would like to appear in "
         << "the table, and query is the query to be asked of "
         << "CORA (something like \"local\" or \"leftlinear\".  "
         << "If you have no queries, just refrain from supplying "
         << "this field." << endl << endl;
    cout << "After the next newline, supply the title for the html "
         << "page, then another newline, and on the lines after "
         << "that, the html text to be placed at the top of the "
         << "page.  If you want to add additional text at the "
         << "bottom of the page, supply another newline and follow "
         << "up with the text you want to be placed at the bottom!"
         << endl << endl;
    cout << "Invoke EVALUATOR with as arguments the files on which "
         << "you want to run CORA (or a directory, in which you "
         << "want to check all files recursively)." << endl << endl;
    return 0;
  }

  if (!read_setup()) return 0;
  for (i = 1; i < argc; i++) {
    if (argv[i][0] != 0 && argv[i][strlen(argv[i])-1] == '/')
      add_directory_contents(argv[i]);
    else files.push_back(argv[i]);
  }

  system("rm -r evaluation/details");
  system("mkdir evaluation/details");

  // create input files
  for (i = 0; i < files.size(); i++) {
    htmlify_input_file(i);
  }

  // determine data for each setup
  for (j = 0; j < setup_names.size(); j++) {
    stringlist test_result;
    stringlist test_result_file;
    intlist test_time;
    for (i = 0; i < files.size(); i++) {
      int time;
      string filename = "test" + str(j) + "_" + str(i) + ".txt";
      string result = run_test(files[i], setup_args[j], filename, time);
      test_result.push_back(result);
      test_time.push_back(time);
      if (result == "YES" || result == "NO")
        test_result_file.push_back(filename);
      else test_result_file.push_back("");
    }
    test_results.push_back(test_result);
    test_result_files.push_back(test_result_file);
    test_times.push_back(test_time);
  }

  // determine answers to queries
  for (j = 0; j < query_names.size(); j++) {
    intlist query_result;
    int time;
    for (i = 0; i < files.size(); i++) {
      string result = run_test(files[i], "-q " + query_args[j], "", time);
      if (result == "YES") query_result.push_back(1);
      else query_result.push_back(0);
    }
    query_results.push_back(query_result);
  }

  // create evaluation page
  make_page();

  return 0;
}

