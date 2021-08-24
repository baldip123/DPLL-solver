#include <iostream>
#include <vector>
#include <string>
#include <set>
#include <vector>
#include <iostream>
#include <fstream> 
#include <sstream>

using namespace std;

enum Assignment {True, False, Unassigned};
enum Answer {Sat, Unsat};

class AssignmentMap {
    private:
        vector<Assignment> PartialAssignment; 
        int numVariables = 0;
    
    public:
        AssignmentMap(int numVariables) {
            this->numVariables = numVariables;
            for(int i = 0; i <= numVariables; i++) {
                PartialAssignment.push_back(Unassigned);
            }
        }

        Assignment GetVariableAssignment(int variable) const {
            if(variable <= 0){
                throw "The variable should be positive, convert literal to positive valuse before passing";
            }
            if(variable > numVariables ) {
                string errorMessage = "The variable ";
                errorMessage += variable;
                errorMessage += " is not in the partial assignment";
                throw errorMessage;
            }
            else {
                return PartialAssignment[variable];
            }
        }

        void SetVariableAssignment(int variable, Assignment value) {
            if(variable <= 0){
                throw "The variable should be positive, convert literal to positive valuse before passing";
            }

            if(abs(variable) > numVariables) {
                string errorMessage = "The literal ";
                errorMessage += variable;
                errorMessage += " is not in the partial assignment";
                throw errorMessage;
            }
            else {
                PartialAssignment[variable] = value;
            }
        }

        Assignment EvaluateLiteral(int literal) const {
            int variable = abs(literal);
            Assignment valueOfVariable = GetVariableAssignment(variable);
            if(valueOfVariable == Unassigned) {
                return Unassigned;
            }
            else if(valueOfVariable == True) {
                if(literal > 0)
                    return True;
                else
                    return False;
            }
            else {
                if(literal > 0) 
                    return False;
                else 
                    return True;
            }

        }

        int GetUnassignedVariable() const {
            //returns 0 if no unassigned variable exists
            for(int variable = 1; variable <= numVariables; variable++) {
                if(GetVariableAssignment(variable) == Unassigned){
                    return variable;
                }
            }

            return 0;
        }
};



class Clause {
    private:
        set<int> literals;
    
    public:
        Clause(set<int> literals) {
            if (literals.empty()){
                throw "Clause can not be empty to begin with";
            }
            else {
                this->literals = literals;
            }
        }

        Assignment Evaluate(const AssignmentMap &Map) const {

            // Fasle iff everything is false
            // True if only one literal is true
            // Unassigned if not true and only one literal is unassigned 

            bool isUnassigned = false;
            for(int literal:literals) {
                if(Map.EvaluateLiteral(literal) == True){
                    return True;
                }
                if(Map.EvaluateLiteral(literal) == Unassigned){
                    isUnassigned = true;
                }
            }

            if(isUnassigned) {
                return Unassigned;
            }
            else {
                return False;
            }
        }

        bool isUnitClause(const AssignmentMap &Map) const {
            int countFalse = 0;
            
            for(int literal: literals) {
                if(Map.EvaluateLiteral(literal) == False){
                    countFalse++; 
                }
            }

            if(countFalse == literals.size() -1) {
                return true;
            }
            else {
                return false;
            }

        }

        int getUnitLiteralIfExists(const AssignmentMap &Map) const {
            //returns 0 if it is not a unit clause
            //returns the literal with sign if it exists

            int countFalse = 0;
            int lastUnassignedLiteral = 0;
            for(int literal: literals) {
                if(Map.EvaluateLiteral(literal) == False){
                    countFalse++; 
                }
                if(Map.EvaluateLiteral(literal) == Unassigned){
                    lastUnassignedLiteral = literal; 
                }
            }

            if(countFalse == literals.size() -1) {
                return lastUnassignedLiteral;
            }
            else {
                return 0;
            }
        }


};

class CNFForumala {
    private:
        vector<Clause> Clauses;
    
    public:
        CNFForumala(vector<Clause> Clauses){
            this->Clauses = Clauses;
        }

        Assignment Evaluate(const AssignmentMap &Map) const {

            // True iff every clause is true
            // False if only one clause is false 
            // Unassigned if even one clause is unassigned and it is not false

            bool isUnassigned = false;
            for(auto &Clause:Clauses) {
                Assignment evaluation = Clause.Evaluate(Map);
                if(evaluation == False){
                    return False;
                }
                if(evaluation == Unassigned){
                    isUnassigned = true;
                }
            }

            if(isUnassigned) {
                return Unassigned;
            }
            else {
                return True;
            }
            
        }

        int getUnitLiteralIfExists(const AssignmentMap &Map) const {
            //returns 0 if there is no unit literal in the whole formula
            //returns the literal with sign if it exists
            for(auto &Clause:Clauses) {
                int unitLiteral = Clause.getUnitLiteralIfExists(Map);
                if(unitLiteral != 0) {
                    // it does exist
                    return unitLiteral;
                }
            }

            return 0;
        }

};

//note that I am not passing M by reference as I am not sure how to make it work correctly
//with backtracking as that was the cause of the error
Answer solve(const CNFForumala& F, AssignmentMap M){
    Assignment Evaluation = F.Evaluate(M);

    if(Evaluation == True)
        return Sat;
    
    if(Evaluation == False)
        return Unsat;

    int unitLiteral = F.getUnitLiteralIfExists(M);
    if(unitLiteral != 0){
        int variable = abs(unitLiteral);
        if(unitLiteral > 0){
            M.SetVariableAssignment(variable, True);
            return solve(F, M);
        }
        else{
            M.SetVariableAssignment(variable, False);
            return solve(F, M);
        }
    }

    //choose unassigned variable, and random bit
    int unassignedVariable = M.GetUnassignedVariable();
    if(unassignedVariable == 0){
        throw "no unassigned variable exists, this does not make sense";
    }

    M.SetVariableAssignment(unassignedVariable, True);
    if(solve(F, M) == Sat){
        return Sat;
    }
    M.SetVariableAssignment(unassignedVariable, False);
    return solve(F, M);
}


set<int> getNumberFromString(string s) {
   stringstream str_strm;
   str_strm << s; //convert the string s into stringstream
   string temp_str;
   int temp_int;
   set<int> literals;
   while(!str_strm.eof()) {
      str_strm >> temp_str; //take words into temp_str one by one
      if(!(stringstream(temp_str) >> temp_int)) { //try to convert string to int
         throw "Wrong format";
      }
      if(temp_int == 0){
          break;
      }
      else{
          literals.insert(temp_int);
      }
   }
   return literals;
}


CNFForumala readFormula(string filename){
    string myText;

    // Read from the text file
    ifstream MyReadFile(filename);

    // Use a while loop together with the getline() function to read the file line by line
    vector<Clause> Clauses;
    while (getline (MyReadFile, myText)) {
    // Output the text from the file
        if(myText[0] == 'c' || myText[0] == 'p'){
        }
        else if(myText[0] == '%'){
            break;
        }
        else{
            auto setofNumbers = getNumberFromString(myText);
            Clauses.push_back(Clause(setofNumbers));
        }
    }

    return CNFForumala(Clauses);
}

int main() {
    bool error = false;
    for(int i = 1; i <= 1000; i++){
        string filename = "tests/uf20-91/uf20-0";
        filename += to_string(i);
        filename += ".cnf";
        CNFForumala formula = readFormula(filename);
        AssignmentMap map(20);
        cout << filename << endl;
        Answer ans = solve(formula, map);
        if(ans != Sat){
            cout << "this is not correct" << endl;
            error = true;
        }
        cout << ans << endl;

    }
    if(error){
        cout << "there was an error" << endl;
    }
    return 0;
}