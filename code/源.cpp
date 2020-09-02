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

enum RS//������ö��
{
	shift,//�ƽ�
	reduce,//��Լ
	accept//����
};

//�ٶ����ս����Ϊһ����д��ĸ���ս����Ϊһ��Сд��ĸ�͸��ַ��ţ�����~����epsilon
class PF//Production formula,����ʽ����
{
public:
	char left;//����ʽ����
	string right;//����ʽ���Ҳ�
	PF(char l, string r)//���캯��
	{
		left = l;
		right = r;
	}
};

class ITEM//��Ŀ��
{
public:
	ITEM();//Ĭ�Ϲ��캯��
	ITEM(int NO);//���캯��
	int NO;//��Ŀ�����
	set<pair<int, int>> production;//��Ŀ����һ��int�������ʽ��ţ��ڶ���int����.��λ��
	set<pair<char, int>> go_to;//����Ŀ��ָ�����Ŀ������һ��char�����ͷ�ϵ��ַ����ڶ���int����ָ�����Ŀ�����
	bool operator<(const ITEM& item)const;//����<���������Ա�ʹ��set
};

ITEM::ITEM()//Ĭ�Ϲ��캯��
{

}

ITEM::ITEM(int NO)//���캯��
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

class action//������
{
public:
	action(RS rs, int num);//��д���캯��
	string ret_action();//���ظö���
	action();//��ʼ
	RS rs;//����
	int num;//�ƽ����ĸ�״̬���������ĸ�����ʽ��Լ
};

action::action(RS rs, int num)//���캯��
{
	this->rs = rs;
	this->num = num;
}

action::action()//Ĭ�Ϲ��캯��
{

}

string action::ret_action()//���ظö���
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

vector<PF> PF_vector;//����ʽ
map<char, set<char> > first;//first��
map<char, set<char> > follow;//follow��
set<ITEM> DFA;//DFA��Ŀ���淶��
vector<map<char, action>> predict_table_action;//SLR1������action
vector<map<char, int>> predict_table_goto;//SLR1������goto
vector<char> A_1;//����ջ
vector<int> A_2;//״̬ջ
vector<char> B;//ʣ�മ
set<char> terminal;//���е��ս��+'$'
set<char> non_terminal;//���еķ��ս��
int B_point = 0, input_len = 0;//B_pointΪ���봮ָ�룬input_lenΪ���봮����

void first_construction()//���첢���first��
{
	while (true)//һֱѭ����first����ֱ�����еķ��ս����first����û�б仯Ϊֹ
	{
		bool not_finished = false;//ʹ��һ��bool���͵ı�����¼first���Ƿ���
		for (int i = 0; i < PF_vector.size(); i++)//�������еĲ���ʽ
		{
			char& left = PF_vector[i].left;
			string& right = PF_vector[i].right;
			for (int j = 0; j < right.size(); j++)//������������ʽ�Ҳ����Ҵ�ǰ����
			{
				if (isupper(right[j]))//�Ƿ��ս��
				{
					bool null_flag = false;
					set<char>& from = first[right[j]];
					set<char>& to = first[left];
					set<char>::iterator it_temp = from.begin();
					int num_old = first[left].size();
					for (; it_temp != from.end(); it_temp++)//�Ѵ�����ս������ʽ�Ҳ��ķ��ս����first���в�Ϊ�յ��ս�����������ս����first����
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
					if (num_new > num_old) //���first��û�б仯��˵��first���Ѿ��������
						not_finished = true;
					if (!null_flag)//���������ս������ʽ�Ҳ��ķ��ս����first����û�пգ��Ͳ������󿴣�ֱ������
						break;
					else if (j == right.size() - 1)
					{
						to.insert('~');
					}
				}
				else//���ս�����
				{
					int num_old = first[left].size();
					first[left].insert(right[j]);//ֱ�ӽ�������ս������ʽ�Ҳ��ķ��ս����ռ��뵽������ս����first����
					int num_new = first[left].size();
					if (num_new > num_old)//���first��û�б仯��˵��first���Ѿ��������
						not_finished = true;
					break;//��Ϊ������ս������ʽ�Ҳ��������ս�����ǿգ����������󿴣�ֱ������
				}
			}
		}
		if (!not_finished)//������еķ��ս����first����û�б仯��˵�����е�first���Ѿ�������ɣ�����whileѭ��
			break;
	}
	//�������õ�first��
	printf("----------------------First��----------------------\n");
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

void add_follow(const char& ch1, const char& ch2)//��ch1��follow�����뵽ch2��follow����
{
	set<char>& from = follow[ch1];
	set<char>& to = follow[ch2];
	set<char>::iterator it = from.begin();
	for (; it != from.end(); it++)
		to.insert(*it);
}

void follow_construction()//���첢���follow��
{
	follow[PF_vector[0].left].insert('$');//���Ƚ���$�����뵽��ʼ����follow���У�����Ĭ�ϵ�һ������Ĳ���ʽ����Ϊ��ʼ��
	while (true)//һֱѭ����follow����ֱ�����еķ��ս����follow����û�б仯Ϊֹ
	{
		bool not_finished = false;//ʹ��һ��bool���͵ı�����¼follow���Ƿ���
		for (int i = 0; i < PF_vector.size(); i++)//�������еĲ���ʽ
		{
			char& left = PF_vector[i].left;
			string& right = PF_vector[i].right;
			bool flag = true;//�����ж��Ƿ�Ҫ������ʽ��߷��ս����follow�����뵽��ǰ���ҵķ��ս����follow����
			for (int j = right.size() - 1; j >= 0; j--)//������������ʽ�Ҳ����ҴӺ���ǰ��
			{
				if (isupper(right[j]))//�Ƿ��ս��
				{
					if (flag)//�ж��Ƿ�Ҫ������ʽ��߷��ս����follow�����뵽��ǰ���ҵķ��ս����follow����
					{
						int num_old = follow[right[j]].size();
						add_follow(left, right[j]);
						if (!first[right[j]].count('~'))
						{
							flag = false;//�����ǰ�ķ��ս����first���в����գ�˵��������ǰ��ķ��ս���������ܽ�
										//����ʽ��߷��ս����follow�����뵽��ǰ���ҵķ��ս����follow����
						}
						int num_new = follow[right[j]].size();
						if (num_new > num_old)//���follow��û�б仯��˵��follow���Ѿ��������
							not_finished = true;
					}
					for (int k = j + 1; k < right.size(); k++)
					{
						if (isupper(right[k]))//�Ƿ��ս��
						{
							bool null_flag = false;
							char id;
							id = right[k];
							set<char>& from = first[id];
							set<char>& to = follow[right[j]];

							set<char>::iterator it_temp = from.begin();
							int num_old = follow[right[j]].size();
							for (; it_temp != from.end(); it_temp++)//�Ѵ�����ս���ĺ���ķ��ս����first���в�Ϊ�յ��ս�����������ս����follow����
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
							if (num_new > num_old) //���follow��û�б仯��˵��follow���Ѿ��������
								not_finished = true;

							if (!null_flag)//���������ս���ĺ���ķ��ս����first����û�пգ��Ͳ������󿴣�ֱ������
								break;
						}
						else//���ս��
						{
							int num_old = follow[right[j]].size();
							follow[right[j]].insert(right[k]);//ֱ�ӽ�������ս��������ս�����뵽������ս����follow����
							int num_new = follow[right[j]].size();
							if (num_new > num_old)//���follow��û�б仯��˵��follow���Ѿ��������
								not_finished = true;
							break;//��Ϊ������ս���������ս�������������󿴣�ֱ������
						}
					}
				}
				else//���ս�����
					flag = false;//�����;�����ս�����Ͳ����ܽ�����ʽ��߷��ս����follow�����뵽��ǰ���ҵķ��ս����follow����
			}
		}
		if (!not_finished)//������еķ��ս����follow����û�б仯��˵�����е�follow���Ѿ�������ɣ�����whileѭ��
			break;
	}
	//�������õ�follow��
	printf("----------------------FOLLOW��----------------------\n");
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

void DFA_construction()//����DFA
{
	int NO = 1;
	ITEM item(0);
	item.production.insert(make_pair(0, 0));//��ʼ��Ŀ
	while (1)//��I0�ıհ�
	{
		bool is_finished = true;
		for (set<pair<int, int>>::iterator it = item.production.begin(); it != item.production.end(); it++)//���ڸ���Ŀ����ÿ������ʽ
		{
			for (int i = 0; i < PF_vector.size(); i++)//�������еĲ���ʽ
			{
				if ((*it).second < PF_vector[(*it).first].right.size() && isupper(PF_vector[(*it).first].right[(*it).second]) && PF_vector[i].left == PF_vector[(*it).first].right[(*it).second])
				{
					int num_old = item.production.size();
					item.production.insert(make_pair(i, 0));//������������Ĳ���ʽ
					int num_new = item.production.size();
					if (num_new > num_old)
					{
						is_finished = false;//�жϸ���Ŀ���Ƿ�����
					}
				}
			}
		}
		if (is_finished)//����Ŀ��������������whileѭ��
		{
			break;
		}
	}
	DFA.insert(item);//��ʼ��Ŀ��I0
	while (1)//һֱѭ����DFA�ıհ���ֱ��DFA��������Ϊֹ
	{
		bool all_finished = true;//������¼DFA�Ƿ�����
		for (set<ITEM>::iterator _it = DFA.begin(); _it != DFA.end(); _it++)//����DFA��ÿ����Ŀ��
		{
			set<char> ch;//���е��ս���ͷ��ս���ļ��ϣ���ȥ~
			set_union(non_terminal.begin(), non_terminal.end(), terminal.begin(), terminal.end(), inserter(ch, ch.begin()));
			ch.erase('$');
			for (set<char>::iterator it1 = ch.begin(); it1 != ch.end(); it1++)//����ÿ�����ţ��ս���ͷ��ս������ȥ~��
			{
				bool flag = false;
				set<pair<int, int>>::iterator it = (*_it).production.begin();
				for (; it != (*_it).production.end(); it++)//�������޷���С��ĺ�����������ŵĲ���ʽ
				{
					if ((*it).second < PF_vector[(*it).first].right.size() && PF_vector[(*it).first].right[(*it).second] == *it1)
					{
						flag = true;//�ҵ�
						break;
					}
				}
				if (flag)//����ҵ�
				{
					ITEM temp_item(DFA.size());
					for (; it != (*_it).production.end(); it++)//������Ŀ�������������������ĺ�����Ŀ
					{
						if ((*it).second < PF_vector[(*it).first].right.size() && PF_vector[(*it).first].right[(*it).second] == *it1)
						{
							temp_item.production.insert(make_pair((*it).first, (*it).second + 1));
						}
					}
					while (1)//�����Ŀ���ıհ���ͬ��
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
						all_finished = false;//�ж�DFA�Ƿ�����
					}
					set<ITEM>::iterator f_it = DFA.find(temp_item);
					ITEM* _it_ = const_cast<ITEM*> (&(*_it));
					_it_->go_to.insert(make_pair(*it1, f_it->NO));//��Դ��Ŀ���������ɵ���Ŀ������
				}
			}
		}
		if (all_finished)//DFA������������whileѭ��
		{
			break;
		}
	}
}

void predict_table_construction()//���첢���SLR1Ԥ�������
{
	for (int l = 0; l < DFA.size(); l++)//����ÿ����Ŀ��
	{
		set<ITEM>::iterator i = DFA.begin();
		for (; i != DFA.end(); i++)
		{
			if (i->NO==l)//�ҵ���l����Ŀ��
			{
				break;
			}
		}
		map<char, action> temp_map1;
		for (set<pair<int, int>>::iterator j = i->production.begin(); j != i->production.end(); j++)//���ڸ���Ŀ����ÿһ����Ŀ
		{
			//С��������Ҳ���ʽ�Ҳ����ǿ�
			if (PF_vector[j->first].right.size() == j->second && PF_vector[j->first].right != "~")
			{
				if (PF_vector[j->first].left == PF_vector[0].left)//�ò���ʽ������ع����ʽ
				{
					temp_map1.insert(pair<char, action>('$', action(accept, -1)));//����
				}
				else//�ò���ʽ��������ع����ʽ
				{
					//�ò���ʽ��follow����Ӧ��action������reduce
					for (set<char>::iterator it = follow[PF_vector[j->first].left].begin(); it != follow[PF_vector[j->first].left].end(); it++)
					{
						temp_map1.insert(pair<char, action>(*it, action(reduce, j->first)));
					}
				}
			}
			else if (PF_vector[j->first].right == "~")//����ʽ�Ҳ��ǿ�
			{
				//ֱ�ӽ��ò���ʽ��follow����Ӧ��action������reduce
				for (set<char>::iterator it = follow[PF_vector[j->first].left].begin(); it != follow[PF_vector[j->first].left].end(); it++)
				{
					temp_map1.insert(pair<char, action>(*it, action(reduce, j->first)));
				}
			}
		}
		map<char, int> temp_map2;
		for (set<pair<char, int>>::iterator j = i->go_to.begin(); j != i->go_to.end(); j++)//���ڸ���Ŀ����ÿһ����ͷ
		{
			if (isupper(j->first))//��������ͷ�ϵķ����Ǵ�д��ĸ��Ҳ���Ƿ��ս��
			{
				temp_map2.insert(pair<char, int>(j->first, j->second));//����goto��
			}
			else//��������ͷ�ϵķ��Ų��Ǵ�д��ĸ��Ҳ�����ս��
			{
				temp_map1.insert(pair<char, action>(j->first, action(shift, j->second)));//���ս����Ӧ��action����shift
			}
		}
		predict_table_action.push_back(temp_map1);//����action��
		predict_table_goto.push_back(temp_map2);//����goto��
	}
	printf("---------------------Ԥ�������---------------------\n");
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
	printf("|%10s|", "״̬");
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

void print_A()//�������ջ
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

void print_B()//���ʣ�മ
{
	string temp = "";
	for (int b = B_point;b < B.size();b++)
		temp += B[b];
	printf("%20s|", temp.c_str());
}

void analyse()//Ԥ��������Ƴ���
{
	int k = 1, n = 0, NO = 0;
	bool flag = true;
	string temp = "";
	A_1.clear();//ÿ�η������Ȱѷ���ջ�ÿ�
	A_2.clear();//ÿ�η������Ȱѷ���ջ�ÿ�
	B_point = 0;//ÿ�η������Ȱ����봮ָ����0
	A_1.push_back('$');//'$'�������ջ
	A_2.push_back(0);//0����״̬ջ
	printf("-------------------------------------------------------------------------------------------\n");
	printf("|%5s|%-20s|%-20s|%20s|%-20s|\n", "����", "״̬ջ", "����ջ", "ʣ���ַ�", "��������");
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
	char ch;//����ķ��������ַ�
	int pf_num, str_num;//����ʽ��Ŀ,��������Ŀ
	in.open("in.txt", ios::in);
	in >> pf_num;
	for (int i = 0; i < pf_num; i++)//�����ķ�
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
	for (int i = 0; i < PF_vector.size(); i++)//����terminal����
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
	for (int i = 0; i < PF_vector.size(); i++)//����non_terminal����
	{
		if (PF_vector[i].left != 'S')
		{
			non_terminal.insert(PF_vector[i].left);
		}
	}
	printf("---------------------�ع��ķ�---------------------\n");
	for (int i = 0; i < PF_vector.size(); i++)
	{
		cout << i << ": " << PF_vector[i].left << "->" << PF_vector[i].right << endl;
	}
	first_construction();
	follow_construction();
	DFA_construction();
	predict_table_construction();
	in >> str_num;
	cout << "Ҫ����" << str_num << "���ַ���" << endl;
	for (int i = 0; i < str_num; i++)
	{
		B.clear();//ÿ�η������Ȱ�ʣ�മ�ÿ�
		do//���������
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
		cout << "����ĵ�" << i + 1 << "���ַ�����";
		for (int j = 0; j < B.size(); j++)
		{
			cout << B[j];
		}
		cout << endl << "�������̣�" << endl;
		analyse();
	}
	in.close();
	system("pause");
	return 0;
}