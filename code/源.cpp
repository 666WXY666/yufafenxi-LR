#include<iostream>
#include<fstream>
#include<conio.h>
#include<stdio.h>
#include<stdlib.h>
#include<cstring>
#include<cstdio>
#include<algorithm>
#include<cstdlib>
#include<vector>
#include<string>
#include<cctype>
#include<map>
#include<set>
#include<iterator>

using namespace std;

enum RS//动作的枚举
{
	shift,//移进
	reduce,//规约
	accept//接受
};

//假定非终结符仅为一个大写字母，终结符仅为一个小写字母和各种符号，且用~代替epsilon
class PF//Production formula,产生式的类
{
public:
	char left;//产生式的左部
	string right;//产生式的右部
	PF(char l, string r)//构造函数
	{
		left = l;
		right = r;
	}
};

class ITEM//项目集
{
public:
	ITEM();//默认构造函数
	ITEM(int NO);//构造函数
	int NO;//项目集编号
	set<pair<int, int>> production;//项目，第一个int代表产生式编号，第二个int代表.的位置
	set<pair<char, int>> go_to;//该项目集指向的项目集，第一个char代表箭头上的字符，第二个int代表指向的项目集编号
	bool operator<(const ITEM& item)const;//重载<操作符，以便使用set
};

ITEM::ITEM()//默认构造函数
{

}

ITEM::ITEM(int NO)//构造函数
{
	this->NO = NO;
}

bool ITEM::operator<(const ITEM& item)const
{
	string str1 = "", str2 = "";
	for (set<pair<int, int>>::iterator it = this->production.begin(); it != this->production.end(); it++)
	{
		str1 += to_string((*it).first) + to_string((*it).second);
	}
	for (set<pair<int, int>>::iterator it = item.production.begin(); it != item.production.end(); it++)
	{
		str2 += to_string((*it).first) + to_string((*it).second);
	}
	return str1 < str2;
}

class action//动作类
{
public:
	action(RS rs, int num);//重写构造函数
	string ret_action();//返回该动作
	action();//初始
	RS rs;//动作
	int num;//移进到哪个状态，或者用哪个产生式规约
};

action::action(RS rs, int num)//构造函数
{
	this->rs = rs;
	this->num = num;
}

action::action()//默认构造函数
{

}

string action::ret_action()//返回该动作
{
	string temp;
	switch (rs)
	{
	case shift:
		temp = "S" + to_string(num);
		break;
	case reduce:
		temp = "R" + to_string(num);
		break;
	case accept:
		temp = "ACC";
		break;
	default:
		temp = "ERROR";
		break;
	}
	return temp;
}

vector<PF> PF_vector;//产生式
map<char, set<char> > first;//first集
map<char, set<char> > follow;//follow集
set<ITEM> DFA;//DFA项目集规范簇
vector<map<char, action>> predict_table_action;//SLR1分析表action
vector<map<char, int>> predict_table_goto;//SLR1分析表goto
vector<char> A_1;//符号栈
vector<int> A_2;//状态栈
vector<char> B;//剩余串
set<char> terminal;//所有的终结符+'$'
set<char> non_terminal;//所有的非终结符
int B_point = 0, input_len = 0;//B_point为输入串指针，input_len为输入串长度

void first_construction()//构造并输出first集
{
	while (true)//一直循环求first集，直到所有的非终结符的first集都没有变化为止
	{
		bool not_finished = false;//使用一个bool类型的变量纪录first集是否变大
		for (int i = 0; i < PF_vector.size(); i++)//遍历所有的产生式
		{
			char& left = PF_vector[i].left;
			string& right = PF_vector[i].right;
			for (int j = 0; j < right.size(); j++)//遍历整个产生式右部，且从前往后看
			{
				if (isupper(right[j]))//是非终结符
				{
					bool null_flag = false;
					set<char>& from = first[right[j]];
					set<char>& to = first[left];
					set<char>::iterator it_temp = from.begin();
					int num_old = first[left].size();
					for (; it_temp != from.end(); it_temp++)//把待求非终结符产生式右部的非终结符的first集中不为空的终结符加入待求非终结符的first集中
					{
						if (*it_temp != '~')
						{
							to.insert(*it_temp);
						}
						else
						{
							null_flag = true;
						}
					}
					int num_new = first[left].size();
					if (num_new > num_old) //如果first集没有变化，说明first集已经构造完成
						not_finished = true;
					if (!null_flag)//如果待求非终结符产生式右部的非终结符的first集中没有空，就不必往后看，直接跳出
						break;
					else if (j == right.size() - 1)
					{
						to.insert('~');
					}
				}
				else//是终结符或空
				{
					int num_old = first[left].size();
					first[left].insert(right[j]);//直接将待求非终结符产生式右部的非终结符或空加入到待求非终结符的first集中
					int num_new = first[left].size();
					if (num_new > num_old)//如果first集没有变化，说明first集已经构造完成
						not_finished = true;
					break;//因为待求非终结符产生式右部遇到了终结符或是空，不必再往后看，直接跳出
				}
			}
		}
		if (!not_finished)//如果所有的非终结符的first集都没有变化，说明所有的first集已经构造完成，跳出while循环
			break;
	}
	//输出构造好的first集
	printf("----------------------First集----------------------\n");
	map<char, set<char> >::iterator it = first.begin();
	for (; it != first.end(); it++)
	{
		printf("%c:{", it->first);
		set<char>& temp = it->second;
		set<char>::iterator it_temp = temp.begin();
		bool flag = false;
		for (; it_temp != temp.end(); it_temp++)
		{
			if (flag) printf(",");
			printf("%c", *it_temp);
			flag = true;
		}
		printf("}\n");
	}
}

void add_follow(const char& ch1, const char& ch2)//将ch1的follow集加入到ch2的follow集中
{
	set<char>& from = follow[ch1];
	set<char>& to = follow[ch2];
	set<char>::iterator it = from.begin();
	for (; it != from.end(); it++)
		to.insert(*it);
}

void follow_construction()//构造并输出follow集
{
	follow[PF_vector[0].left].insert('$');//首先将‘$’加入到起始符的follow集中，这里默认第一个输入的产生式的左部为起始符
	while (true)//一直循环求follow集，直到所有的非终结符的follow集都没有变化为止
	{
		bool not_finished = false;//使用一个bool类型的变量纪录follow集是否变大
		for (int i = 0; i < PF_vector.size(); i++)//遍历所有的产生式
		{
			char& left = PF_vector[i].left;
			string& right = PF_vector[i].right;
			bool flag = true;//用来判断是否要将产生式左边非终结符的follow集加入到当前查找的非终结符的follow集中
			for (int j = right.size() - 1; j >= 0; j--)//遍历整个产生式右部，且从后往前看
			{
				if (isupper(right[j]))//是非终结符
				{
					if (flag)//判断是否要将产生式左边非终结符的follow集加入到当前查找的非终结符的follow集中
					{
						int num_old = follow[right[j]].size();
						add_follow(left, right[j]);
						if (!first[right[j]].count('~'))
						{
							flag = false;//如果当前的非终结符的first集中不含空，说明所有它前面的非终结符均不可能将
										//产生式左边非终结符的follow集加入到当前查找的非终结符的follow集中
						}
						int num_new = follow[right[j]].size();
						if (num_new > num_old)//如果follow集没有变化，说明follow集已经构造完成
							not_finished = true;
					}
					for (int k = j + 1; k < right.size(); k++)
					{
						if (isupper(right[k]))//是非终结符
						{
							bool null_flag = false;
							char id;
							id = right[k];
							set<char>& from = first[id];
							set<char>& to = follow[right[j]];

							set<char>::iterator it_temp = from.begin();
							int num_old = follow[right[j]].size();
							for (; it_temp != from.end(); it_temp++)//把待求非终结符的后面的非终结符的first集中不为空的终结符加入待求非终结符的follow集中
							{
								if (*it_temp != '~')
								{
									to.insert(*it_temp);
								}
								else
								{
									null_flag = true;
								}
							}
							int num_new = follow[right[j]].size();
							if (num_new > num_old) //如果follow集没有变化，说明follow集已经构造完成
								not_finished = true;

							if (!null_flag)//如果待求非终结符的后面的非终结符的first集中没有空，就不必往后看，直接跳出
								break;
						}
						else//是终结符
						{
							int num_old = follow[right[j]].size();
							follow[right[j]].insert(right[k]);//直接将待求非终结符后面的终结符加入到待求非终结符的follow集中
							int num_new = follow[right[j]].size();
							if (num_new > num_old)//如果follow集没有变化，说明follow集已经构造完成
								not_finished = true;
							break;//因为待求非终结符后面是终结符，不必再往后看，直接跳出
						}
					}
				}
				else//是终结符或空
					flag = false;//如果中途遇到终结符，就不可能将产生式左边非终结符的follow集加入到当前查找的非终结符的follow集中
			}
		}
		if (!not_finished)//如果所有的非终结符的follow集都没有变化，说明所有的follow集已经构造完成，跳出while循环
			break;
	}
	//输出构造好的follow集
	printf("----------------------FOLLOW集----------------------\n");
	map<char, set<char> >::iterator it = follow.begin();
	for (; it != follow.end(); it++)
	{
		printf("%c:{", it->first);
		set<char>& temp = it->second;
		set<char>::iterator it_temp = temp.begin();
		bool flag = false;
		for (; it_temp != temp.end(); it_temp++)
		{
			if (flag) printf(",");
			printf("%c", *it_temp);
			flag = true;
		}
		printf("}\n");
	}
}

void DFA_construction()//构造DFA
{
	int NO = 1;
	ITEM item(0);
	item.production.insert(make_pair(0, 0));//初始项目
	while (1)//求I0的闭包
	{
		bool is_finished = true;
		for (set<pair<int, int>>::iterator it = item.production.begin(); it != item.production.end(); it++)//对于该项目集的每个产生式
		{
			for (int i = 0; i < PF_vector.size(); i++)//对于所有的产生式
			{
				if ((*it).second < PF_vector[(*it).first].right.size() && isupper(PF_vector[(*it).first].right[(*it).second]) && PF_vector[i].left == PF_vector[(*it).first].right[(*it).second])
				{
					int num_old = item.production.size();
					item.production.insert(make_pair(i, 0));//加入符合条件的产生式
					int num_new = item.production.size();
					if (num_new > num_old)
					{
						is_finished = false;//判断该项目集是否增大
					}
				}
			}
		}
		if (is_finished)//该项目集不再增大，跳出while循环
		{
			break;
		}
	}
	DFA.insert(item);//初始项目集I0
	while (1)//一直循环求DFA的闭包，直到DFA不再增大为止
	{
		bool all_finished = true;//用来记录DFA是否增大
		for (set<ITEM>::iterator _it = DFA.begin(); _it != DFA.end(); _it++)//对于DFA的每个项目集
		{
			set<char> ch;//所有的终结符和非终结符的集合，除去~
			set_union(non_terminal.begin(), non_terminal.end(), terminal.begin(), terminal.end(), inserter(ch, ch.begin()));
			ch.erase('$');
			for (set<char>::iterator it1 = ch.begin(); it1 != ch.end(); it1++)//对于每个符号（终结符和非终结符，除去~）
			{
				bool flag = false;
				set<pair<int, int>>::iterator it = (*_it).production.begin();
				for (; it != (*_it).production.end(); it++)//查找有无符合小点的后面是这个符号的产生式
				{
					if ((*it).second < PF_vector[(*it).first].right.size() && PF_vector[(*it).first].right[(*it).second] == *it1)
					{
						flag = true;//找到
						break;
					}
				}
				if (flag)//如果找到
				{
					ITEM temp_item(DFA.size());
					for (; it != (*_it).production.end(); it++)//将新项目集加入所有满足条件的核心项目
					{
						if ((*it).second < PF_vector[(*it).first].right.size() && PF_vector[(*it).first].right[(*it).second] == *it1)
						{
							temp_item.production.insert(make_pair((*it).first, (*it).second + 1));
						}
					}
					while (1)//求该项目集的闭包，同上
					{
						bool is_finished = true;
						for (set<pair<int, int>>::iterator it = temp_item.production.begin(); it != temp_item.production.end(); it++)
						{
							for (int i = 0; i < PF_vector.size(); i++)
							{
								if ((*it).second < PF_vector[(*it).first].right.size() && isupper(PF_vector[(*it).first].right[(*it).second]) && PF_vector[i].left == PF_vector[(*it).first].right[(*it).second])
								{
									int num_old = temp_item.production.size();
									temp_item.production.insert(make_pair(i, 0));
									int num_new = temp_item.production.size();
									if (num_new > num_old)
									{
										is_finished = false;
									}
								}
							}
						}
						if (is_finished)
						{
							break;
						}
					}
					int size_old = DFA.size();
					DFA.insert(temp_item);
					int size_new = DFA.size();
					if (size_new > size_old)
					{
						all_finished = false;//判断DFA是否增大
					}
					set<ITEM>::iterator f_it = DFA.find(temp_item);
					ITEM* _it_ = const_cast<ITEM*> (&(*_it));
					_it_->go_to.insert(make_pair(*it1, f_it->NO));//将源项目集和新生成的项目集连接
				}
			}
		}
		if (all_finished)//DFA不再增大，跳出while循环
		{
			break;
		}
	}
}

void predict_table_construction()//构造并输出SLR1预测分析表
{
	for (int l = 0; l < DFA.size(); l++)//对于每个项目集
	{
		set<ITEM>::iterator i = DFA.begin();
		for (; i != DFA.end(); i++)
		{
			if (i->NO==l)//找到第l个项目集
			{
				break;
			}
		}
		map<char, action> temp_map1;
		for (set<pair<int, int>>::iterator j = i->production.begin(); j != i->production.end(); j++)//对于该项目集的每一个项目
		{
			//小点在最后且产生式右部不是空
			if (PF_vector[j->first].right.size() == j->second && PF_vector[j->first].right != "~")
			{
				if (PF_vector[j->first].left == PF_vector[0].left)//该产生式如果是拓广产生式
				{
					temp_map1.insert(pair<char, action>('$', action(accept, -1)));//接受
				}
				else//该产生式如果不是拓广产生式
				{
					//该产生式左部follow集对应的action都加入reduce
					for (set<char>::iterator it = follow[PF_vector[j->first].left].begin(); it != follow[PF_vector[j->first].left].end(); it++)
					{
						temp_map1.insert(pair<char, action>(*it, action(reduce, j->first)));
					}
				}
			}
			else if (PF_vector[j->first].right == "~")//产生式右部是空
			{
				//直接将该产生式左部follow集对应的action都加入reduce
				for (set<char>::iterator it = follow[PF_vector[j->first].left].begin(); it != follow[PF_vector[j->first].left].end(); it++)
				{
					temp_map1.insert(pair<char, action>(*it, action(reduce, j->first)));
				}
			}
		}
		map<char, int> temp_map2;
		for (set<pair<char, int>>::iterator j = i->go_to.begin(); j != i->go_to.end(); j++)//对于该项目集的每一个箭头
		{
			if (isupper(j->first))//如果这个箭头上的符号是大写字母，也就是非终结符
			{
				temp_map2.insert(pair<char, int>(j->first, j->second));//加入goto表
			}
			else//如果这个箭头上的符号不是大写字母，也就是终结符
			{
				temp_map1.insert(pair<char, action>(j->first, action(shift, j->second)));//该终结符对应的action加入shift
			}
		}
		predict_table_action.push_back(temp_map1);//加入action表
		predict_table_goto.push_back(temp_map2);//加入goto表
	}
	printf("---------------------预测分析表---------------------\n");
	for (int i = 0; i <= (terminal.size() + non_terminal.size() + 1) * 11; i++)
		printf("-");
	printf("\n");
	printf("|%10s|", "");
	for (int i = 0; i < 11 * terminal.size() / 2 - 3; i++)
	{
		cout << ' ';
	}
	cout << "action";
	for (int i = 0; i < 11 * terminal.size() - 11 * terminal.size() / 2 - 4; i++)
	{
		cout << ' ';
	}
	cout << '|';
	for (int i = 0; i < 11 * non_terminal.size() / 2 - 2; i++)
	{
		cout << ' ';
	}
	cout << "goto";
	for (int i = 0; i < 11 * non_terminal.size() - 11 * non_terminal.size() / 2 - 3; i++)
	{
		cout << ' ';
	}
	cout << '|' << endl;
	printf("|%10s|", "状态");
	for (int i = 1; i <= (terminal.size() + non_terminal.size()) * 11; i++)
		printf("-");
	printf("\n");
	printf("|%10s|", "");
	;
	for (set<char>::iterator it = terminal.begin(); it != terminal.end(); it++)
		printf("%10c|", *it);
	for (set<char>::iterator it = non_terminal.begin(); it != non_terminal.end(); it++)
		printf("%10c|", *it);
	printf("\n");
	for (int i = 0; i <= (terminal.size() + non_terminal.size() + 1) * 11; i++)
		printf("-");
	printf("\n");
	for (int i = 0; i < predict_table_action.size(); i++)
	{
		printf("|%10d|", i);
		for (set<char>::iterator it = terminal.begin(); it != terminal.end(); it++)
			if (predict_table_action[i].count(*it))
			{
				printf("%10s|", predict_table_action[i][*it].ret_action().c_str());
			}
			else printf("%10s|", "");
		for (set<char>::iterator it = non_terminal.begin(); it != non_terminal.end(); it++)
			if (predict_table_goto[i].count(*it))
			{
				printf("%10d|", predict_table_goto[i][*it]);
			}
			else printf("%10s|", "");
		printf("\n");
		for (int i = 0; i <= (terminal.size() + non_terminal.size() + 1) * 11; i++)
			printf("-");
		printf("\n");
	}
}

void print_A()//输出分析栈
{
	string temp2 = "";
	for (int a = 0;a < A_2.size();a++)
		temp2 = temp2 + to_string(A_2[a]) + " ";
	printf("%-20s|", temp2.c_str());
	string temp1 = "";
	for (int a = 0;a < A_1.size();a++)
		temp1 += A_1[a];
	printf("%-20s|", temp1.c_str());
}

void print_B()//输出剩余串
{
	string temp = "";
	for (int b = B_point;b < B.size();b++)
		temp += B[b];
	printf("%20s|", temp.c_str());
}

void analyse()//预测分析控制程序
{
	int k = 1, n = 0, NO = 0;
	bool flag = true;
	string temp = "";
	A_1.clear();//每次分析都先把分析栈置空
	A_2.clear();//每次分析都先把分析栈置空
	B_point = 0;//每次分析都先把输入串指针置0
	A_1.push_back('$');//'$'进入符号栈
	A_2.push_back(0);//0进入状态栈
	printf("-------------------------------------------------------------------------------------------\n");
	printf("|%5s|%-20s|%-20s|%20s|%-20s|\n", "步骤", "状态栈", "符号栈", "剩余字符", "分析动作");
	printf("-------------------------------------------------------------------------------------------\n");
	do
	{
		printf("|%5d|", k++);
		print_A();
		print_B();
		switch (predict_table_action[A_2[A_2.size() - 1]][B[B_point]].rs)
		{
		case shift:
			temp = "shift " + to_string(predict_table_action[A_2[A_2.size() - 1]][B[B_point]].num);
			A_1.push_back(B[B_point]);
			A_2.push_back(predict_table_action[A_2[A_2.size() - 1]][B[B_point]].num);
			B_point++;
			break;
		case reduce:
			temp = "reduce by " + string(1, PF_vector[predict_table_action[A_2[A_2.size() - 1]][B[B_point]].num].left) + "->" + PF_vector[predict_table_action[A_2[A_2.size() - 1]][B[B_point]].num].right;
			n = PF_vector[predict_table_action[A_2[A_2.size() - 1]][B[B_point]].num].right.size();
			NO = predict_table_action[A_2[A_2.size() - 1]][B[B_point]].num;
			for (int i = 0; i < n; i++)
			{
				A_1.pop_back();
				A_2.pop_back();
			}
			A_1.push_back(PF_vector[NO].left);
			A_2.push_back(predict_table_goto[A_2[A_2.size() - 1]][A_1[A_1.size() - 1]]);
			break;
		case accept:
			flag = false;
			temp = "ACCEPT!";
			break;
		default:
			flag = false;
			temp = "ERROR!";
			break;
		}
		printf("%-20s|\n", temp.c_str());
	} while (flag);
	printf("-------------------------------------------------------------------------------------------\n");
}

int main()
{
	ifstream in;
	char ch;//读入的分析串的字符
	int pf_num, str_num;//产生式数目,分析串数目
	in.open("in.txt", ios::in);
	in >> pf_num;
	for (int i = 0; i < pf_num; i++)//读入文法
	{
		char left, temp;
		string right;
		in >> left >> temp >> temp >> right;
		if (i == 0)
		{
			PF_vector.push_back(PF('S', string(1, left)));
		}
		PF_vector.push_back(PF(left, right));
	}
	for (int i = 0; i < PF_vector.size(); i++)//生成terminal集合
	{
		for (int j = 0; j < PF_vector[i].right.size(); j++)
		{
			if (!isupper(PF_vector[i].right[j]))
			{
				if (PF_vector[i].right[j] != '~')
				{
					terminal.insert(PF_vector[i].right[j]);
				}
			}
		}
	}
	terminal.insert('$');
	for (int i = 0; i < PF_vector.size(); i++)//生成non_terminal集合
	{
		if (PF_vector[i].left != 'S')
		{
			non_terminal.insert(PF_vector[i].left);
		}
	}
	printf("---------------------拓广文法---------------------\n");
	for (int i = 0; i < PF_vector.size(); i++)
	{
		cout << i << ": " << PF_vector[i].left << "->" << PF_vector[i].right << endl;
	}
	first_construction();
	follow_construction();
	DFA_construction();
	predict_table_construction();
	in >> str_num;
	cout << "要分析" << str_num << "个字符串" << endl;
	for (int i = 0; i < str_num; i++)
	{
		B.clear();//每次分析都先把剩余串置空
		do//读入分析串
		{
			in >> ch;
			if (ch==EOF)
			{
				cout << "ERROR!" << endl;
				return 1;
			}
			B.push_back(ch);
			input_len++;
		} while (ch != '$');
		cout << "输入的第" << i + 1 << "个字符串：";
		for (int j = 0; j < B.size(); j++)
		{
			cout << B[j];
		}
		cout << endl << "分析过程：" << endl;
		analyse();
	}
	in.close();
	system("pause");
	return 0;
}