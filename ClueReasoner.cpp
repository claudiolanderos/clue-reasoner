#include "ClueReasoner.h"
using namespace std;

int ClueReasoner::GetPlayerNum(string player)
{
	if (player == case_file)
		return num_players;
	
	for (int i = 0; i < num_players; i++)
		if (player == players[i])
			return i;
			
	cout<<"Illegal player: "<<player<<endl;
	return -1;
}
int ClueReasoner::GetCardNum(string card)
{
	for (int i = 0; i < num_cards; i++)
		if (card == cards[i])
			return i;
			
	cout<<"Illegal card: "<<card<<endl;
	return -1;
}

string ClueReasoner::QueryString(int return_code)
{
	if (return_code == kFalse)
		return "n";
	else if (return_code == kTrue)
		return "Y";
	else
		return "-";
}

void ClueReasoner::PrintNotepad()
{
	for (int i = 0; i < num_players; i++)
		cout<<"\t"<<players[i];
	cout<<"\t"<<case_file<<endl;
	
	for (int i = 0; i < num_cards; i++)
	{
		cout<<cards[i]<<"\t";
		for (int j = 0; j < num_players; j++)
			cout<<QueryString(Query(players[j], cards[i]))<<"\t";
		
		cout<<QueryString(Query(case_file, cards[i]))<<endl;
	}
}
	
void ClueReasoner::AddInitialClauses()
{
	/* The following code is given as an example to show how to create Clauses and post them to the solver. SatSolver.h uses the following typedefs:
		typedef int Literal;
		typedef std::vector<Literal> Clause;
		
	That is, a Literal (a propositional variable or its negation) is defined as a positive or a negative (meaning that it is in negated form, as in -p or -q) integer, and a Clause is defined as a vector of Literals.
	
	The function GetPairNum(p, c) returns the literal that corresponds to card c being at location p (either a player's hand or the case_file). 
	See ClueReasoner.h, lines 7-29 for a definition of the arrays and variables that you can use in your implementation. 
	*/

	// Each card is in at least one place (including the case file).
	for (int c = 0; c < num_cards; c++)	// Iterate over all cards.
	{
		Clause clause;
		for (int p = 0; p <= num_players; p++)	// Iterate over all players, including the case file (as a possible place for a card).
			clause.push_back(GetPairNum(p, c));
		
		solver->AddClause(clause);
	}
        
	// If a card is in one place, it cannot be in another place.
    for (int c = 0; c < num_cards; c++)	// Iterate over all cards.
    {
        Clause clause;
        for (int p = 0; p <= num_players; p++)
        {
            for (int x = 0; x <= num_players; x++)
            {
                if(p != x)
                {
                    clause.push_back(GetPairNum(p, c)*-1);
                    clause.push_back(GetPairNum(x, c)*-1);
                    solver->AddClause(clause);
                    clause.clear();
                }
            }
        }
    }
    
	// At least one card of each category is in the case file.
    Clause clause;
    for(int s = 0; s < num_suspects; s++)
    {
        clause.push_back(GetPairNum(GetPlayerNum(case_file), GetCardNum(suspects[s])));
    }
    solver->AddClause(clause);
    clause.clear();
    
    for(int w = 0; w < num_weapons; w++)
    {
        clause.push_back(GetPairNum(GetPlayerNum(case_file), GetCardNum(weapons[w])));
    }
    solver->AddClause(clause);
    clause.clear();

    for(int r = 0; r < num_rooms; r++)
    {
        clause.push_back(GetPairNum(GetPlayerNum(case_file), GetCardNum(rooms[r])));
    }
    solver->AddClause(clause);
    clause.clear();
    
	// No two cards in each category can both be in the case file.
    for(int s = 0; s < num_suspects; s++)
    {
        for(int x = 0; x < num_suspects; x++)
        {
            if(s != x)
            {
                clause.push_back(GetPairNum(GetPlayerNum(case_file), GetCardNum(suspects[s]))*-1);
                clause.push_back(GetPairNum(GetPlayerNum(case_file), GetCardNum(suspects[x]))*-1);
                solver->AddClause(clause);
                clause.clear();
            }
        }
    }
    
    for(int w = 0; w < num_weapons; w++)
    {
        for(int x = 0; x < num_weapons; x++)
        {
            if(w != x)
            {
                clause.push_back(GetPairNum(GetPlayerNum(case_file), GetCardNum(weapons[w]))*-1);
                clause.push_back(GetPairNum(GetPlayerNum(case_file), GetCardNum(weapons[x]))*-1);
                solver->AddClause(clause);
                clause.clear();
            }
        }
    }
    
    for(int r = 0; r < num_rooms; r++)
    {
        for(int x = 0; x < num_rooms; x++)
        {
            if(r != x)
            {
                clause.push_back(GetPairNum(GetPlayerNum(case_file), GetCardNum(rooms[r]))*-1);
                clause.push_back(GetPairNum(GetPlayerNum(case_file), GetCardNum(rooms[x]))*-1);
                solver->AddClause(clause);
                clause.clear();
            }
        }
    }
}
void ClueReasoner::Hand(string player, string cards[3])
{
	// GetPlayerNum returns the index of the player in the players array (not the suspects array). Remember that the players array is sorted wrt the order that the players play. Also note that, player_num (not to be confused with num_players) is a private variable of the ClueReasoner class that is initialized when this function is called.
	player_num = GetPlayerNum(player);
	
    //Add the known cards as simple clauses
    Clause c;
    
    c.push_back(GetPairNum(player_num, GetCardNum(cards[0])));
    solver->AddClause(c);   c.clear();
    
    c.push_back(GetPairNum(player_num, GetCardNum(cards[1])));
    solver->AddClause(c);   c.clear();
    
    c.push_back(GetPairNum(player_num, GetCardNum(cards[2])));
    solver->AddClause(c);   c.clear();
}
void ClueReasoner::Suggest(string suggester, string card1, string card2, string card3, string refuter, string card_shown)
{
	// Note that in the Java implementation, the refuter and the card_shown can be NULL. 
	// In this C++ implementation, NULL is translated to be the empty string "".
	// To check if refuter is NULL or card_shown is NULL, you should use if(refuter == "") or if(card_shown == ""), respectively.
	
    int player = GetPlayerNum(suggester);
    int inBetween = player;
    Clause clause;
    
    //Refuter has the card shown or at least one of the suggested cards.
    if(refuter != "")
    {
        if(card_shown != "")
        {
            clause.push_back(GetPairNum(refuter, card_shown));
            solver->AddClause(clause);
            clause.clear();
        }
        else {
            clause.push_back(GetPairNum(refuter, card1));
            clause.push_back(GetPairNum(refuter, card2));
            clause.push_back(GetPairNum(refuter, card3));
            solver->AddClause(clause);
            clause.clear();
        }
    }else{
        return;
    }
    
    //Implement in between players case
    while(inBetween != GetPlayerNum(refuter))
    {
        if(inBetween == num_players-1){
            inBetween = 0;
        }
        else {
            inBetween++;
        }
        if(inBetween == GetPlayerNum(refuter) || inBetween == GetPlayerNum(suggester)){
            break;
        }
        
        //We know players in between suggester and refuter do not have those cards.
        clause.push_back(GetPairNum(inBetween, GetCardNum(card1))*-1);
        solver->AddClause(clause);
        clause.clear();
        clause.push_back(GetPairNum(inBetween, GetCardNum(card2))*-1);
        solver->AddClause(clause);
        clause.clear();
        clause.push_back(GetPairNum(inBetween, GetCardNum(card3))*-1);
        solver->AddClause(clause);
        clause.clear();
    }
}
void ClueReasoner::Accuse(string suggester, string card1, string card2, string card3, bool is_correct)
{
	// TO BE IMPLEMENTED AS AN EXERCISE
}
