#include <stack>
#include <cmath>
#include <set>
#include <string>
#include <iostream>
#include <fstream>
#include <vector>
#include <ctime>
#include <cstring>
#include <queue>
#include <vector>
#include <stdexcept>
#include <algorithm>
#include <unordered_map>
#include <cstdlib>
#include <sstream>
#ifdef _BOTZONE_ONLINE
#include "jsoncpp/json.h"
#else
#include "jsoncpp/json.h"
#endif

using std::string;
using std::cin;
using std::cout;
using std::endl;
using std::flush;
using std::getline;
using std::queue;
using std::vector;
using std::pair;

std::ofstream debug("debug.txt", std::ofstream::out);

namespace TankGame
{
    using std::stack;
    using std::set;
    using std::istream;

#ifdef _MSC_VER
#pragma region 常量定义和说明
#endif

    enum GameResult
    {
        NotFinished = -2,
        Draw = -1,
        Blue = 0,
        Red = 1
    };

    enum FieldItem
    {
        None = 0,
        Brick = 1,
        Steel = 2,
        Base = 4,
        Blue0 = 8,
        Blue1 = 16,
        Red0 = 32,
        Red1 = 64,
        Water = 128
    };

    template<typename T> inline T operator~ (T a) { return (T)~(int)a; }
    template<typename T> inline T operator| (T a, T b) { return (T)((int)a | (int)b); }
    template<typename T> inline T operator& (T a, T b) { return (T)((int)a & (int)b); }
    template<typename T> inline T operator^ (T a, T b) { return (T)((int)a ^ (int)b); }
    template<typename T> inline T& operator|= (T& a, T b) { return (T&)((int&)a |= (int)b); }
    template<typename T> inline T& operator&= (T& a, T b) { return (T&)((int&)a &= (int)b); }
    template<typename T> inline T& operator^= (T& a, T b) { return (T&)((int&)a ^= (int)b); }

    enum Action
    {
        Invalid = -2,
        Stay = -1,
        Up, Right, Down, Left,
        UpShoot, RightShoot, DownShoot, LeftShoot
    };

    // 坐标左上角为原点（0, 0），x 轴向右延伸，y 轴向下延伸
    // Side（对战双方） - 0 为蓝，1 为红
    // Tank（每方的坦克） - 0 为 0 号坦克，1 为 1 号坦克
    // Turn（回合编号） - 从 1 开始

    const int fieldHeight = 9, fieldWidth = 9, sideCount = 2, tankPerSide = 2;

    // 基地的横坐标
    const int baseX[sideCount] = { fieldWidth / 2, fieldWidth / 2 };

    // 基地的纵坐标
    const int baseY[sideCount] = { 0, fieldHeight - 1 };

    const int dx[4] = { 0, 1, 0, -1 }, dy[4] = { -1, 0, 1, 0 };
    const FieldItem tankItemTypes[sideCount][tankPerSide] = {
        { Blue0, Blue1 },{ Red0, Red1 }
    };

    int maxTurn = 100;

#ifdef _MSC_VER
#pragma endregion

#pragma region 工具函数和类
#endif

    inline bool ActionIsMove(Action x)
    {
        return x >= Up && x <= Left;
    }

    inline bool ActionIsShoot(Action x)
    {
        return x >= UpShoot && x <= LeftShoot;
    }

    inline bool ActionDirectionIsOpposite(Action a, Action b)
    {
        return a >= Up && b >= Up && (a + 2) % 4 == b % 4;
    }

    inline bool CoordValid(int x, int y)
    {
        return x >= 0 && x < fieldWidth && y >= 0 && y < fieldHeight;
    }

    // 判断 item 是不是叠在一起的多个坦克
    inline bool HasMultipleTank(FieldItem item)
    {
        // 如果格子上只有一个物件，那么 item 的值是 2 的幂或 0
        // 对于数字 x，x & (x - 1) == 0 当且仅当 x 是 2 的幂或 0
        return !!(item & (item - 1));
    }

    inline int GetTankSide(FieldItem item)
    {
        return item == Blue0 || item == Blue1 ? Blue : Red;
    }

    inline int GetTankID(FieldItem item)
    {
        return item == Blue0 || item == Red0 ? 0 : 1;
    }

    // 获得动作的方向
    inline int ExtractDirectionFromAction(Action x)
    {
        if (x >= Up)
            return x % 4;
        return -1;
    }

    // 物件消失的记录，用于回退
    struct DisappearLog
    {
        FieldItem item;

        // 导致其消失的回合的编号
        int turn;

        int x, y;
        bool operator< (const DisappearLog& b) const
        {
            if (x == b.x)
            {
                if (y == b.y)
                    return item < b.item;
                return y < b.y;
            }
            return x < b.x;
        }
    };

#ifdef _MSC_VER
#pragma endregion

#pragma region TankField 主要逻辑类
#endif

    class TankField
    {
    public:
        //!//!//!// 以下变量设计为只读，不推荐进行修改 //!//!//!//

        // 游戏场地上的物件（一个格子上可能有多个坦克）
        FieldItem gameField[fieldHeight][fieldWidth] = {};

        // 坦克是否存活
        bool tankAlive[sideCount][tankPerSide] = { { true, true },{ true, true } };

        // 基地是否存活
        bool baseAlive[sideCount] = { true, true };

        // 坦克横坐标，-1表示坦克已炸
        int tankX[sideCount][tankPerSide] = {
            { fieldWidth / 2 - 2, fieldWidth / 2 + 2 },{ fieldWidth / 2 + 2, fieldWidth / 2 - 2 }
        };

        // 坦克纵坐标，-1表示坦克已炸
        int tankY[sideCount][tankPerSide] = { { 0, 0 },{ fieldHeight - 1, fieldHeight - 1 } };

        // 当前回合编号
        int currentTurn = 1;

        // 我是哪一方
        int mySide;

        // 用于回退的log
        stack<DisappearLog> logs;

        // 过往动作（previousActions[x] 表示所有人在第 x 回合的动作，第 0 回合的动作没有意义）
        Action previousActions[101][sideCount][tankPerSide] = { { { Stay, Stay },{ Stay, Stay } } };

        //!//!//!// 以上变量设计为只读，不推荐进行修改 //!//!//!//

        // 本回合双方即将执行的动作，需要手动填入
        Action nextAction[sideCount][tankPerSide] = { { Invalid, Invalid },{ Invalid, Invalid } };

        // 判断行为是否合法（出界或移动到非空格子算作非法）
        // 未考虑坦克是否存活
        bool ActionIsValid(int side, int tank, Action act)
        {
            if (act == Invalid)
                return false;
            if (act > Left && previousActions[currentTurn - 1][side][tank] > Left) // 连续两回合射击
                return false;
            if (act == Stay || act > Left)
                return true;
            int x = tankX[side][tank] + dx[act],
                y = tankY[side][tank] + dy[act];
            return CoordValid(x, y) && gameField[y][x] == None;// water cannot be stepped on
        }

        // 判断 nextAction 中的所有行为是否都合法
        // 忽略掉未存活的坦克
        bool ActionIsValid()
        {
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    if (tankAlive[side][tank] && !ActionIsValid(side, tank, nextAction[side][tank]))
                        return false;
            return true;
        }

    private:
        void _destroyTank(int side, int tank)
        {
            tankAlive[side][tank] = false;
            tankX[side][tank] = tankY[side][tank] = -1;
        }

        void _revertTank(int side, int tank, DisappearLog& log)
        {
            int &currX = tankX[side][tank], &currY = tankY[side][tank];
            if (tankAlive[side][tank])
                gameField[currY][currX] &= ~tankItemTypes[side][tank];
            else
                tankAlive[side][tank] = true;
            currX = log.x;
            currY = log.y;
            gameField[currY][currX] |= tankItemTypes[side][tank];
        }
    public:

        // 执行 nextAction 中指定的行为并进入下一回合，返回行为是否合法
        bool DoAction()
        {
            if (!ActionIsValid())
                return false;

            // 1 移动
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                {
                    Action act = nextAction[side][tank];

                    // 保存动作
                    previousActions[currentTurn][side][tank] = act;
                    if (tankAlive[side][tank] && ActionIsMove(act))
                    {
                        int &x = tankX[side][tank], &y = tankY[side][tank];
                        FieldItem &items = gameField[y][x];

                        // 记录 Log
                        DisappearLog log;
                        log.x = x;
                        log.y = y;
                        log.item = tankItemTypes[side][tank];
                        log.turn = currentTurn;
                        logs.push(log);

                        // 变更坐标
                        x += dx[act];
                        y += dy[act];

                        // 更换标记（注意格子可能有多个坦克）
                        gameField[y][x] |= log.item;
                        items &= ~log.item;
                    }
                }

            // 2 射♂击!
            set<DisappearLog> itemsToBeDestroyed;
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                {
                    Action act = nextAction[side][tank];
                    if (tankAlive[side][tank] && ActionIsShoot(act))
                    {
                        int dir = ExtractDirectionFromAction(act);
                        int x = tankX[side][tank], y = tankY[side][tank];
                        bool hasMultipleTankWithMe = HasMultipleTank(gameField[y][x]);
                        while (true)
                        {
                            x += dx[dir];
                            y += dy[dir];
                            if (!CoordValid(x, y))
                                break;
                            FieldItem items = gameField[y][x];
                            //tank will not be on water, and water will not be shot, so it can be handled as None
                            if (items != None && items != Water)
                            {
                                // 对射判断
                                if (items >= Blue0 &&
                                    !hasMultipleTankWithMe && !HasMultipleTank(items))
                                {
                                    // 自己这里和射到的目标格子都只有一个坦克
                                    Action theirAction = nextAction[GetTankSide(items)][GetTankID(items)];
                                    if (ActionIsShoot(theirAction) &&
                                        ActionDirectionIsOpposite(act, theirAction))
                                    {
                                        // 而且我方和对方的射击方向是反的
                                        // 那么就忽视这次射击
                                        break;
                                    }
                                }

                                // 标记这些物件要被摧毁了（防止重复摧毁）
                                for (int mask = 1; mask <= Red1; mask <<= 1)
                                    if (items & mask)
                                    {
                                        DisappearLog log;
                                        log.x = x;
                                        log.y = y;
                                        log.item = (FieldItem)mask;
                                        log.turn = currentTurn;
                                        itemsToBeDestroyed.insert(log);
                                    }
                                break;
                            }
                        }
                    }
                }

            for (auto& log : itemsToBeDestroyed)
            {
                switch (log.item)
                {
                case Base:
                {
                    int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
                    baseAlive[side] = false;
                    break;
                }
                case Blue0:
                    _destroyTank(Blue, 0);
                    break;
                case Blue1:
                    _destroyTank(Blue, 1);
                    break;
                case Red0:
                    _destroyTank(Red, 0);
                    break;
                case Red1:
                    _destroyTank(Red, 1);
                    break;
                case Steel:
                    continue;
                default:
                    ;
                }
                gameField[log.y][log.x] &= ~log.item;
                logs.push(log);
            }

            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    nextAction[side][tank] = Invalid;

            currentTurn++;
            return true;
        }

        // 回到上一回合
        bool Revert()
        {
            if (currentTurn == 1)
                return false;

            currentTurn--;
            while (!logs.empty())
            {
                DisappearLog& log = logs.top();
                if (log.turn == currentTurn)
                {
                    logs.pop();
                    switch (log.item)
                    {
                    case Base:
                    {
                        int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
                        baseAlive[side] = true;
                        gameField[log.y][log.x] = Base;
                        break;
                    }
                    case Brick:
                        gameField[log.y][log.x] = Brick;
                        break;
                    case Blue0:
                        _revertTank(Blue, 0, log);
                        break;
                    case Blue1:
                        _revertTank(Blue, 1, log);
                        break;
                    case Red0:
                        _revertTank(Red, 0, log);
                        break;
                    case Red1:
                        _revertTank(Red, 1, log);
                        break;
                    default:
                        ;
                    }
                }
                else
                    break;
            }
            return true;
        }

        // 游戏是否结束？谁赢了？
        GameResult GetGameResult()
        {
            bool fail[sideCount] = {};
            for (int side = 0; side < sideCount; side++)
                if ((!tankAlive[side][0] && !tankAlive[side][1]) || !baseAlive[side])
                    fail[side] = true;
            if (fail[0] == fail[1])
                return fail[0] || currentTurn > maxTurn ? Draw : NotFinished;
            if (fail[Blue])
                return Red;
            return Blue;
        }

        /* 三个 int 表示场地 01 矩阵（每个 int 用 27 位表示 3 行）
           initialize gameField[][]
           brick>water>steel
        */
        TankField() = default;
        TankField(int hasBrick[3],int hasWater[3],int hasSteel[3], int mySide) : mySide(mySide)
        {
            for (int i = 0; i < 3; i++)
            {
                int mask = 1;
                for (int y = i * 3; y < (i + 1) * 3; y++)
                {
                    for (int x = 0; x < fieldWidth; x++)
                    {
                        if (hasBrick[i] & mask)
                            gameField[y][x] = Brick;
                        else if(hasWater[i] & mask)
                            gameField[y][x] = Water;
                        else if(hasSteel[i] & mask)
                            gameField[y][x] = Steel;
                        mask <<= 1;
                    }
                }
            }
            for (int side = 0; side < sideCount; side++)
            {
                for (int tank = 0; tank < tankPerSide; tank++)
                    gameField[tankY[side][tank]][tankX[side][tank]] = tankItemTypes[side][tank];
                gameField[baseY[side]][baseX[side]] = Base;
            }
        }
        TankField(const TankField & ob)
            :currentTurn(ob.currentTurn), logs(ob.logs),mySide(ob.mySide)
            {
                memcpy(gameField, ob.gameField,sizeof(ob.gameField));
                memcpy(tankAlive, ob.tankAlive, sizeof(ob.tankAlive));
                memcpy(tankX, ob.tankX, sizeof(ob.tankX));
                memcpy(tankY, ob.tankY, sizeof(ob.tankY));
                memcpy(baseAlive, ob.baseAlive, sizeof(ob.baseAlive));
                memcpy(previousActions, ob.previousActions, sizeof(ob.previousActions));
            } 
        TankField & operator = (const TankField &ob)
        {
            currentTurn = ob.currentTurn;
            logs = ob.logs;
            mySide = ob.mySide;
            memcpy(gameField, ob.gameField,sizeof(ob.gameField));
            memcpy(tankAlive, ob.tankAlive, sizeof(ob.tankAlive));
            memcpy(tankX, ob.tankX, sizeof(ob.tankX));
            memcpy(tankY, ob.tankY, sizeof(ob.tankY));
            memcpy(baseAlive, ob.baseAlive, sizeof(ob.baseAlive));
            memcpy(previousActions, ob.previousActions, sizeof(ob.previousActions));
            return *this;
        }

        // 打印场地
        void DebugPrint()
        {
#ifndef _BOTZONE_ONLINE
            const string side2String[] = { "蓝", "红" };
            const string boolean2String[] = { "已炸", "存活" };
            const char* boldHR = "==============================";
            const char* slimHR = "------------------------------";
            cout << boldHR << endl
                << "图例：" << endl
                << ". - 空\t# - 砖\t% - 钢\t* - 基地\t@ - 多个坦克" << endl
                << "b - 蓝0\tB - 蓝1\tr - 红0\tR - 红1\tW - 水" << endl //Tank2 feature
                << slimHR << endl;
            for (int y = 0; y < fieldHeight; y++)
            {
                for (int x = 0; x < fieldWidth; x++)
                {
                    switch (gameField[y][x])
                    {
                    case None:
                        cout << '.';
                        break;
                    case Brick:
                        cout << '#';
                        break;
                    case Steel:
                        cout << '%';
                        break;
                    case Base:
                        cout << '*';
                        break;
                    case Blue0:
                        cout << 'b';
                        break;
                    case Blue1:
                        cout << 'B';
                        break;
                    case Red0:
                        cout << 'r';
                        break;
                    case Red1:
                        cout << 'R';
                        break;
                    case Water:
                        cout << 'W';
                        break;
                    default:
                        cout << '@';
                        break;
                    }
                }
                cout << endl;
            }
            cout << slimHR << endl;
            for (int side = 0; side < sideCount; side++)
            {
                cout << side2String[side] << "：基地" << boolean2String[baseAlive[side]];
                for (int tank = 0; tank < tankPerSide; tank++)
                    cout << ", 坦克" << tank << boolean2String[tankAlive[side][tank]];
                cout << endl;
            }
            cout << "当前回合：" << currentTurn << "，";
            GameResult result = GetGameResult();
            if (result == -2)
                cout << "游戏尚未结束" << endl;
            else if (result == -1)
                cout << "游戏平局" << endl;
            else
                cout << side2String[result] << "方胜利" << endl;
            cout << boldHR << endl;
#endif
        }

        bool operator!= (const TankField& b) const
        {

            for (int y = 0; y < fieldHeight; y++)
                for (int x = 0; x < fieldWidth; x++)
                    if (gameField[y][x] != b.gameField[y][x])
                        return true;

            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                {
                    if (tankX[side][tank] != b.tankX[side][tank])
                        return true;
                    if (tankY[side][tank] != b.tankY[side][tank])
                        return true;
                    if (tankAlive[side][tank] != b.tankAlive[side][tank])
                        return true;
                }

            if (baseAlive[0] != b.baseAlive[0] ||
                baseAlive[1] != b.baseAlive[1])
                return true;

            if (currentTurn != b.currentTurn)
                return true;

            return false;
        }
    } *nullField;

#ifdef _MSC_VER
#pragma endregion
#endif

    TankField *field;

#ifdef _MSC_VER
#pragma region 与平台交互部分
#endif

    // 内部函数
    namespace Internals
    {
        Json::Reader reader;
#ifdef _BOTZONE_ONLINE
        Json::FastWriter writer;
#else
        Json::StyledWriter writer;
#endif

        void _processRequestOrResponse(Json::Value& value, bool isOpponent)
        {
            if (value.isArray())
            {
                if (!isOpponent)
                {
                    for (int tank = 0; tank < tankPerSide; tank++)
                        field->nextAction[field->mySide][tank] = (Action)value[tank].asInt();
                }
                else
                {
                    for (int tank = 0; tank < tankPerSide; tank++)
                        field->nextAction[1 - field->mySide][tank] = (Action)value[tank].asInt();
                    field->DoAction();
                }
            }
            else
            {
                // 是第一回合，裁判在介绍场地
                int hasBrick[3],hasWater[3],hasSteel[3];
                for (int i = 0; i < 3; i++){//Tank2 feature(???????????????)
                    hasWater[i] = value["waterfield"][i].asInt();
                    hasBrick[i] = value["brickfield"][i].asInt();
                    hasSteel[i] = value["steelfield"][i].asInt();
                }
                field = new TankField(hasBrick,hasWater,hasSteel,value["mySide"].asInt());
            }
        }

        // 请使用 SubmitAndExit 或者 SubmitAndDontExit
        void _submitAction(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "")
        {
            Json::Value output(Json::objectValue), response(Json::arrayValue);
            response[0U] = tank0;
            response[1U] = tank1;
            output["response"] = response;
            if (!debug.empty())
                output["debug"] = debug;
            if (!data.empty())
                output["data"] = data;
            if (!globalData.empty())
                output["globalData"] = globalData;
            cout << writer.write(output) << endl;
        }
    }

    // 从输入流（例如 cin 或者 fstream）读取回合信息，存入 TankField，并提取上回合存储的 data 和 globaldata
    // 本地调试的时候支持多行，但是最后一行需要以没有缩进的一个"}"或"]"结尾
    void ReadInput(istream& in, string& outData, string& outGlobalData)
    {
        Json::Value input;
        string inputString;
        do
        {
            getline(in, inputString);
        } while (inputString.empty());
#ifndef _BOTZONE_ONLINE
        // 猜测是单行还是多行
        char lastChar = inputString[inputString.size() - 1];
        if (lastChar != '}' && lastChar != ']')
        {
            // 第一行不以}或]结尾，猜测是多行
            string newString;
            do
            {
                getline(in, newString);
                inputString += newString;
            } while (newString != "}" && newString != "]");
        }
#endif
        Internals::reader.parse(inputString, input);

        if (input.isObject())
        {
            Json::Value requests = input["requests"], responses = input["responses"];
            if (!requests.isNull() && requests.isArray())
            {
                size_t i, n = requests.size();
                for (i = 0; i < n; i++)
                {
                    Internals::_processRequestOrResponse(requests[i], true);
                    if (i < n - 1)
                        Internals::_processRequestOrResponse(responses[i], false);
                }
                outData = input["data"].asString();
                outGlobalData = input["globaldata"].asString();
                return;
            }
        }
        Internals::_processRequestOrResponse(input, true);
    }

    // 提交决策并退出，下回合时会重新运行程序
    void SubmitAndExit(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "")
    {
        Internals::_submitAction(tank0, tank1, debug, data, globalData);
        exit(0);
    }

    // 提交决策，下回合时程序继续运行（需要在 Botzone 上提交 Bot 时选择“允许长时运行”）
    // 如果游戏结束，程序会被系统杀死
    void SubmitAndDontExit(Action tank0, Action tank1)
    {
        Internals::_submitAction(tank0, tank1);
        field->nextAction[field->mySide][0] = tank0;
        field->nextAction[field->mySide][1] = tank1;
        cout << ">>>BOTZONE_REQUEST_KEEP_RUNNING<<<" << endl;
    }
#ifdef _MSC_VER
#pragma endregion
#endif
}
int RandBetween(int from, int to)
{
    return rand() % (to - from) + from;
}

TankGame::Action RandAction(int tank)
{
    while (true)
    {
        auto act = (TankGame::Action)RandBetween(TankGame::Stay, TankGame::LeftShoot + 1);
        if (TankGame::field->ActionIsValid(TankGame::field->mySide, tank, act))
            return act;
    }
}
struct Action{
    TankGame::Action a[2];
    using ACT = typename TankGame::Action;
    Action(int _=-1, int b=-1)
    {
        a[0] = (ACT)_, a[1] = (ACT)b;
    }
    TankGame::Action & operator [] (const int &x) {
        return a[x];
    }
};

std::ostream & operator << (std::ostream &out, Action &b)
{
    out << " (" << b[0] << ", " << b[1] <<") " ;
    return out;
}

double sigmoid(double x) { return 1./(1+exp(-x)); }

class Judger {
    public:
        TankGame::TankField *field;
        bool havebeenDebug = 1; 
        int spfa(int side, int  id)
        {
            std::queue< std::pair<int, int> > q;
            bool vis[TankGame::fieldHeight][TankGame::fieldWidth] = {0};
            int cost[TankGame::fieldHeight][TankGame::fieldWidth];
            memset(cost, 127, sizeof(cost));
            cost[field->tankY[side][id]][field->tankX[side][id]] = 0;
            q.push(std::pair<int,int>(field->tankY[side][id], field->tankX[side][id]));
            vis[field->tankY[side][id]][field->tankX[side][id]]= 1; 
            while (!q.empty()) {
                int y = q.front().first;
                int x = q.front().second;
                q.pop();
                vis[y][x] = 0;
                for (int k=0; k<4; ++k)
                {
                    int yy = y + TankGame::dy[k];
                    int xx = x + TankGame::dx[k]; 
                    if (!TankGame::CoordValid(xx, yy)) continue;
                    if (field->gameField[yy][xx] == TankGame::Steel
                        || field->gameField[yy][xx]== TankGame::Water
                        || field->gameField[yy][xx] ==TankGame::Red0
                        || field->gameField[yy][xx] ==TankGame::Red1
                        || field->gameField[yy][xx] == TankGame::Blue0
                        || field->gameField[yy][xx] == TankGame::Blue1)
                        continue;
                    int c = 0;
                    if (field->gameField[yy][xx] == TankGame::Brick)
                        c = 2;
                    else c = 1;
                    if (cost[y][x] + c < cost[yy][xx])
                    {
                        cost[yy][xx] = cost[y][x] + c;
                        if (!vis[yy][xx])
                        {
                            vis[yy][xx] = 1;
                            q.push(std::pair<int, int> (yy, xx));
                        }
                    }
                }
            }
            int x = TankGame::baseX[1-side];
            int y = TankGame::baseY[1-side];
            int xyDelta = abs(x - field->tankX[side][id]) + abs(y - field->tankY[side][id]);
            int min = cost[y][x];
            for (int k = 0; k < 4; ++k) {
                int co = 0;
                int xx = x, yy =  y;
                for (int i=1; 1; ++i)
                {
                    xx += TankGame::dx[k];
                    yy += TankGame::dy[k];
                    if (field->gameField[yy][xx] == TankGame::Steel
                    || !TankGame::CoordValid(xx, yy))
                        break;
                    if (field->gameField[yy][xx] == TankGame::Brick)
                        co += 2;
                    min = std::min(min, cost[yy][xx] + co);
                }
            }
            // if (side == 0)
            // {
            //     debug << field->tankX[side][id] << ' ' << field->tankY[side][id] << ": " << min<< ' ' << xyDelta << endl;
            // }
            return min + xyDelta / 2;
        }
        double getDisScore(TankGame::TankField *Field)
        {
            // Field->DebugPrint();

            
            int side = Field->mySide;
            TankGame::GameResult res = Field->GetGameResult();
            int D1, D2;
            field = Field;
            D1 = spfa(side, 0);
            D2 = spfa(side, 1);
            if (D1 > D2) std::swap(D1, D2);
            // cout << D1 << ", " << D2 << endl;
            double val =  20- (1.*D1 + 0.5 * D2);
            return val;
        }
        double dp(int side)
        {
            double cost[TankGame::fieldHeight][TankGame::fieldWidth];
            double dis[TankGame::fieldHeight][TankGame::fieldWidth];
            bool vs[TankGame::fieldHeight][TankGame::fieldWidth];
            using pii  = typename std::pair<int, int>;

            pii q[85*10];
            int head = 0, tail = 0;

            memset(dis, 127, sizeof(dis));
            memset(vs, 0, sizeof(vs));
            int mnY = std::min(field->tankY[side][0], field->tankY[side][1]);
            int mxY = std::max(field->tankY[side][0], field->tankY[side][1]);
            
            dis[TankGame::baseY[1-side]][TankGame::baseX[1-side]] = 0;

            for (int k=0; k<4; ++k)
            {
                int y = TankGame::baseY[1], x = TankGame::baseX[1];
                double cost = 1, val = 1.; 
                for (; 1; )
                {
                    y = y + TankGame::dy[k], x = x + TankGame::dx[k];
                    if ((!TankGame::CoordValid(x, y))
                    ||  (field->gameField[y][x] == TankGame::Steel)
                    ||  (field->gameField[y][x] & (8+16+32+64)) )
                        break;
                    if (field->gameField[y][x] == TankGame::Water)
                        continue;
                    dis[y][x] = cost;
                    if (!vs[y][x])
                    {
                        vs[y][x] = 1;
                        q[tail] = pii(y, x); tail += 1;
                    }
                    if (field->gameField[y][x] == TankGame::Brick)
                       val = val * 1.1, cost += val*2;
                }
            }
            
            for (int i = 0; i<TankGame::fieldHeight; ++i)
                for (int j= 0; j<TankGame::fieldWidth; ++j)
                {
                    if ((field->gameField[i][j] == TankGame::Steel)
                    || (field->gameField[i][j] == TankGame::Water)
                    || (field->gameField[i][j] & (8+16+32+64))
                    )
                        cost[i][j] = 100;
                    if (field->gameField[i][j] == TankGame::Brick)
                    {
                        if (side == 0)
                            cost[i][j] = i >= mnY? 1 : 2;
                        else
                            cost[i][j] = i <= mxY? 1: 2;
                    }
                }
            while (head < tail)
            {
                int y = q[head].first, x = q[head].second;
                head += 1;
                vs[y][x] = 0;
                for (int k=0; k<4; ++k)
                {
                    int xx = x + TankGame::dx[k];
                    int yy = y + TankGame::dy[k]; 
                    if (TankGame::CoordValid(xx, yy) == 0)
                        continue;
                    if (dis[yy][xx] > dis[y][x] + cost[y][x] + 1)
                    {
                        dis[yy][xx] = dis[y][x] + cost[y][x] + 1;
                        if (vs[yy][xx] == 0)
                        {
                            vs[yy][xx] = 1;
                            q[tail] = pii(yy, xx);
                            tail += 1;
                        }
                    }
                }
            }
            double d1 = dis[field->tankY[side][0]][field->tankX[side][0]];
            double d2 = dis[field->tankY[side][1]][field->tankX[side][1]];
            if (d1 > d2) std::swap(d1, d2);
            
            double protectBricks = 0;
            int x = TankGame::baseX[1-side], y = TankGame::baseY[1-side];
            int x1 = x, x2 = x;
            int y1, y2;
            for (y1 = 1; 1; ++y1)
            {
                if (field->gameField[y + TankGame::dy[side * 2] * y1][x] != TankGame::Brick)
                {
                    -- y1; 
                    break;
                }
            }
            if (havebeenDebug == 0)
                cout << y1 << endl;
            y2 = y1;
            protectBricks = y1;

            for (; 1; ) 
            {
                x1 -= 1, x2 += 1;
                if (x1 < 0) break;
                int y1_ = 0, y2_ = 0;
                if (havebeenDebug == 0)
                    cout << y + TankGame::dy[side*2] * y1_ << ' ' << x1 << endl
                    << y + TankGame::dy[side*2] * y2_ << ' ' << x2 << endl;
                for (; 1; ++y1_)
                    if (field->gameField[y + TankGame::dy[side*2] * y1_][x1] != TankGame::Brick)
                    {
                        y1_ -= 1;
                        break;
                    }
                for (; 1; ++y2_)
                    if (field->gameField[y + TankGame::dy[side*2] * y2_][x2] != TankGame::Brick)
                    {
                        y2_ -= 1;
                        break;
                    }
                y1 = std::min(y1, y1_);
                y2 = std::min(y1, y2_);
                if (havebeenDebug==0)
                    cout << y1 << ' ' << y2 << endl;
                protectBricks += std::max(0, y1 + y2);
            }
            if (!havebeenDebug) {
                havebeenDebug = 1;
                field->DebugPrint();
                for (int i=0; i<TankGame::fieldHeight; ++i)
                {
                    for (int j=0; j<TankGame::fieldWidth; ++j)
                        cout << dis[i][j] << ' ';
                    cout << endl;
                }
                for (int i=0; i<TankGame::fieldHeight; ++i)
                {
                    for (int j=0; j<TankGame::fieldWidth; ++j)
                        cout << cost[i][j] << ' ';
                    cout << endl; 
                }
                cout << "D1 = " << d1 << " " <<  "D2 = " << d2 << endl;
                cout << "protectBricks = " << protectBricks << endl;
                cout << "return value is " << d1 + 0.8 * d2  - protectBricks * 0.3 << endl;
            }
            return d1 + 0.8 * d2  - protectBricks * 0.3;
        }
        double deltaScale(double a, double b) 
        {
            if (a < b) std::swap(a, b);
            double delta = a - b;
            return delta / a;
        }
        double getScore(TankGame::TankField *Field)
        {
            int side = Field->mySide;
            TankGame::GameResult res = Field->GetGameResult();
            if (res != TankGame::NotFinished)
            {
                if (res == TankGame::Draw) return 0.5;
                else if (res == side) return 1;
                else return 0;
            }
            int myAlive = 0, eneAlive = 0;
            for (int i=0; i<2; ++i) {
                myAlive += Field->tankAlive[side][i];
                eneAlive += Field->tankAlive[1-side][i];
            }
            field = Field;
            // D1 = spfa(side, 0);
            // D2 = spfa(side, 1);
            // D3 = spfa( + Safe_down - Safe_up1-side, 0);
            // D4 = spfa(1-side, 1);
            // if (D1 > D2) std::swap(D1, D2);
            // if (D3 > D4) std::swap(D3, D4);
            // double val = (1.*D3 + 0.8 * D4) - (1.*D1 + 0.8 * D2);
            double up =  dp(0);
            double down = dp(1); 
            double val = 0; 
            if (side == 0) val = down - up;
            else val = up - down; 
            if (deltaScale(up, down) < 0.2)
                val += 5.*(myAlive-eneAlive);
            else
            {
                if ((up < down) == (side == 0))
                    val += 3. * (myAlive - eneAlive);
                else
                    val += 20. * (myAlive - eneAlive);
            }

            return sigmoid(val);
        }

        int countAliveDelta(TankGame::TankField *Field)
        {
            int side = Field->mySide;
            int myAlive = 0, eneAlive = 0;
            for (int i=0; i<2; ++i) {
                myAlive += Field->tankAlive[side][i];
                eneAlive += Field->tankAlive[1-side][i];
            }
            return myAlive - eneAlive;
        }
        std::vector< std::pair<Action, double> > getBestBlocks(TankGame::TankField *Field, int t, int w = 64)
        {
            int side = Field->mySide;
            field = Field;
            std::vector< std::pair<Action, double> > returnV;
            for (int i = -1; i< 8; ++i)
                for (int j = -1; j<8; ++j)
                {
                    Field->nextAction[side][0 ] = (TankGame::Action) i;
                    Field->nextAction[side][1 ] = (TankGame::Action) j;
                    Field->nextAction[1-side][0] = (TankGame::Action) -1;
                    Field->nextAction[1-side][1] = (TankGame::Action) -1;
                    if (Field->ActionIsValid())
                        returnV.push_back(std::pair<Action, double> (Action(i, j), 1));
                }
            // for (int i=-1; i<8; ++i)
            //     for (int j =-1; j<8; ++j)  {
            //         Field->nextAction[side][0] = (TankGame::Action) i;
            //         Field->nextAction[side][1] = (TankGame::Action) j;
            //         Field->nextAction[1-side][0] = (TankGame::Action) -1;
            //         Field->nextAction[1-side][1] = (TankGame::Action) -1;
            //         if (Field->ActionIsValid()) {
            //             Field->DoAction();
            //             TankGame::GameResult res = Field->GetGameResult();
            //             double Dis = getDisScore(Field);
            //             Field->Revert();
            //             // std::vector<int> Deltas; 
            //             // for (int h = -1; h<8; ++h)
            //             //     for (int l = -1; l<8; ++l)
            //             //     {
            //             //         Field->nextAction[side][0] = (TankGame::Action) i;
            //             //         Field->nextAction[side][1] = (TankGame::Action) j;
            //             //         Field->nextAction[1-side][0] = (TankGame::Action) h;
            //             //         Field->nextAction[1-side][1] = (TankGame::Action) l;
            //             //         if (Field->ActionIsValid()) {
            //             //             Field->DoAction();
            //             //             Deltas.push_back(countAliveDelta(Field));
            //             //             Field->Revert();
            //             //         }
            //             //     }
            //             // if(Deltas.size() < w) w = Deltas.size();
            //             // std::sort(Deltas.begin(), Deltas.end()); 
            //             double Alive = 0;
            //             // for (int h = 0; h<w; ++h)
            //             //     Alive += Deltas[h];
            //             // Alive /= 0.05 * w; 
            //             returnV.push_back(std::pair<Action, double>(Action(i,j), sigmoid(Dis+Alive)));
                    
            //         }
            //     }
            
            // using pAD = typename std::pair<Action, double>;
            // std::sort(returnV.begin(), returnV.end(), 
            // [](const pAD &a, const pAD &b)
            // {
            //     return a.second>b.second;
            // });

            while(returnV.size() > t)
                returnV.pop_back();

            // debug << "bestActions:" << endl;
            // for (auto a:returnV)
            // {
            //     debug << a.first << ": " << a.second << ";   ";
            // }
            // debug << endl << "============================" << endl;
            
            return returnV;
        }
} fastJudger;

class FastAgent
{
    public:
        int t; 
        FastAgent(int ft)
            : t(ft) {}
        Action getAction(TankGame::TankField *Field) {
            auto bestBlocks = fastJudger.getBestBlocks(Field, t);
            auto action = bestBlocks[rand() % bestBlocks.size()];
            return action.first ;
        }
};
class VirtualGame
{
    public:
        int maxTurns, initTurns;
        TankGame::TankField Field;
        VirtualGame() = default;
        VirtualGame(TankGame::TankField *Field)
            :Field(*Field), initTurns(Field->currentTurn) {}
        double run(FastAgent *fa, int maxTurns = -1, bool verbose = false)
        {
            // debug <<"VirtualGame.run:" ;
            double result;
            // std::vector<double> results;
            while (true)
            {
                TankGame::GameResult res = Field.GetGameResult();
                if (res != TankGame::NotFinished)
                {
                    if (res == Field.mySide)
                        result = 1;
                    else if (res == TankGame::Draw)
                        result = 0.5; 
                    else result = 0;
                    // results.push_back(result);
                    // break;
                    return result;
                }
                else result = -1;
                // results.push_back(fastJudger.getScore(&Field));
                if (maxTurns != -1 && Field.currentTurn >= maxTurns + initTurns)
                {
                    return sigmoid(fastJudger.getScore(&Field));
                }
                // double lastTime = clock();
                Action myAction = fa->getAction(&Field);
                Field.mySide ^= 1;
                Action enemyAction = fa->getAction(&Field);
                Field.mySide ^= 1;
                // debug << "{ " << myAction << enemyAction <<" }" << "; " << endl;
                int side = Field.mySide;
                Field.nextAction[side][0] = myAction[0];
                Field.nextAction[side][1] = myAction[1];
                Field.nextAction[side^1][0] = enemyAction[0];
                Field.nextAction[side^1][1] = enemyAction[1];
                if (!Field.DoAction())
                    throw std::runtime_error("stimulate error: the best is invalid");
            }
            /*
            std::sort(results.begin(), results.end());
            double returnValue = 0;
            double theta[20], sum = 0;
            int t = results.size();
            for (int i=0; i<t; ++i)
                theta[i] = 1./(i+1), sum += theta[i];
            for (int i=0; i<t; ++i)
                theta[i] /= sum, returnValue = results[i] * theta[i];
            */
            // return results[results.size() -1];
        }
};
class MCTSAgent
{
    public:
        double s;
        int t;
        int maxTurns;
        bool verbose;
        FastAgent fast;
        MCTSAgent() = default;
        MCTSAgent(double s, int t, int ft, int maxTurns,
            bool verbose = false)
        : s(s), t(t), fast(ft), maxTurns(maxTurns)
        , verbose(verbose) {} 
        static const int SIMULATION_NUM = 100000;
        Action getAction(TankGame::TankField *Field)
        {
            MCTnode root = MCTnode(Field, s, t);
            long long startTime = 0;
            int it;
            for (it = 0; it < SIMULATION_NUM; ++it)
            {
                double second = (double) (clock() - startTime)/ CLOCKS_PER_SEC;
                if (second > 0.9)
                    break;
                simulate(&root);
            }
            int action = 0;
            for (int i=0; i<root.actionAgent[Field->mySide].actionNum; ++i)
            {

                if (verbose)
                {
                    debug << i <<": " << root.actionAgent[Field->mySide].validMove[i]
                        << " " <<  root.actionAgent[Field->mySide].winSum[i] 
                        <<'/' << root.actionAgent[Field->mySide].visitSum[i] << "="
                        << 1. * root.actionAgent[Field->mySide].winSum[i]/root.actionAgent[Field->mySide].visitSum[i] << endl;
                }
                if (root.actionAgent[Field->mySide].visitSum[i]
                > root.actionAgent[Field->mySide].visitSum[action])
                    action = i;
            }

            debug << it << ' ';
            debug << action << ' ';
            debug << root.actionAgent[Field->mySide].actionNum << ' ';
            if (verbose)
            {
                debug << root.actionAgent[Field->mySide].winSum[action] 
                <<'/' << root.actionAgent[Field->mySide].visitSum[action] << "="
                << 1. * root.actionAgent[Field->mySide].winSum[action]/root.actionAgent[Field->mySide].visitSum[action] << endl;
            }
            Action bestAction(root.actionAgent[Field->mySide].validMove[action]);
            return bestAction;
        } 
        std::vector< std::pair<Action, std::pair<double,double> > > getActions(TankGame::TankField *Field)
        {
            MCTnode root = MCTnode(Field, s, t);
            long long startTime = 0;
            int it;
            for (it = 0; it < SIMULATION_NUM; ++it)
            {
                double second = (double) (clock() - startTime)/ CLOCKS_PER_SEC;
                if (second > 0.9)
                    break;
                simulate(&root);
            }
            std::vector<std::pair<int,double> > actions;
            for (int i=0; i<root.actionAgent[Field->mySide].actionNum; ++i)
            {

                if (verbose)
                {
                    debug << i <<": " << root.actionAgent[Field->mySide].validMove[i]
                        << " " <<  root.actionAgent[Field->mySide].winSum[i] 
                        <<'/' << root.actionAgent[Field->mySide].visitSum[i] << "="
                        << 1. * root.actionAgent[Field->mySide].winSum[i]/root.actionAgent[Field->mySide].visitSum[i] << endl;
                }
                actions.push_back(std::pair<int,int>(i, root.actionAgent[Field->mySide].visitSum[i]));
            }
            sort(actions.begin(), actions.end(), [](const std::pair<int,int> &pa, const std::pair<int, int> &pb)
            {
                return pa.second > pb.second;
            });
            int t = std::min((int)actions.size(), 5);
            std::vector< std::pair<Action, std::pair<double,double> > > returnVal;
            for(int i=0; i<t; ++i)
                returnVal.push_back( std::pair<Action, std::pair<double, double> >
                    (root.actionAgent[Field->mySide].validMove[actions[i].first], std::pair<double,double>
                        (root.actionAgent[Field->mySide].winSum[actions[i].first], root.actionAgent[Field->mySide].visitSum[actions[i].first]))
                );
            return returnVal;
       } 
 
    private:
        struct ActionAgent
        {
            int actionNum;
            vector<double> visitSum, winSum;
            vector<double> prior;
            vector<Action> validMove;
            ActionAgent() = default;
            ActionAgent(TankGame::TankField *Field, double s, int t)
            {
                auto actionRank = fastJudger.getBestBlocks(Field, t);
                double upper = actionRank.front().second;
                validMove.reserve(actionRank.size());
                prior.reserve(actionRank.size());
                double sum = 0;
                for (auto &p : actionRank)
                {
                    validMove.push_back(p.first);
                    prior.push_back(exp((p.second-upper)*s));
                    sum += prior.back();
                }
                for (auto &p : prior)
                    p /= sum;
                actionNum = validMove.size();
                visitSum = vector<double>(actionNum, 0);
                winSum = vector<double>(actionNum, 0);
            }
            int getBest(double parentVisit)
            {
                double uct = -std::numeric_limits<double>::max();
                double logp = log(parentVisit + 1);
                vector<int> possibles;
                for (int i = 0; i<actionNum; ++i)
                {
                    double p = winSum[i] /(visitSum[i] + 1);
                    double var = std::min(sqrt(2 * logp / (visitSum[i] + 1)) + p*(1-p), 0.25);
                    double nuct = p + sqrt(var * logp / (visitSum[i] + 1)) + 5.*prior[i] / (visitSum[i] + 1);

                    // debug << validMove[i]<<" : " << prior[i] << ", " << nuct << endl; 

                    if (nuct > uct)
                    {
                        uct = nuct ;
                        possibles.clear();
                        possibles.push_back(i);
                    }
                    else if (nuct == uct)
                        possibles.push_back(i);
                }
                return possibles.empty() ? -1 : possibles[rand()%possibles.size()];
            }
        };
        struct MCTnode
        {
            double result;
            double visitCount;
            double winCount;
            TankGame::TankField Field;
            ActionAgent actionAgent[2];
            std::unordered_map<int, MCTnode *> nxt;
            MCTnode() {}
            MCTnode(TankGame::TankField *field, double s, int t)
            {
                
                TankGame::GameResult res = field->GetGameResult();
                if (res == TankGame::NotFinished) {
                    result = -1;
                }
                else {
                    if (res == field->mySide)
                        result = 1;
                    else if (res == 1-field->mySide)
                        result = 0;
                    else result = 0.5;
                    return;
                }
            
                visitCount = winCount = 0;
                Field = *field;
                actionAgent[Field.mySide] = ActionAgent(&Field, s, t);
                Field.mySide ^= 1;
                actionAgent[Field.mySide] = ActionAgent(&Field, s, t);
                Field.mySide ^= 1;
            }
        };
        void simulate(MCTnode *pNode)
        {
            static MCTnode *pNodeStk[110];
            static int action0Stk[110];
            static int action1Stk[110];
            int cnt = 0;
            double result;
            while (true)
            {
                // debug << "simulate!" << endl;
                if (pNode->result != -1)
                {
                    pNode->visitCount += 1;
                    pNode->winCount += pNode->result;
                    result = pNode->result;
                    break;
                }
                int action0 = pNode->actionAgent[0].getBest(pNode->visitCount);
                int action1 = pNode->actionAgent[1].getBest(pNode->visitCount);

                // if (verbose)
                //     debug << "-> ( " << action0 << ",  " << action1 << " )";

                pNodeStk[cnt] = pNode;
                action0Stk[cnt]  = action0;
                action1Stk[cnt] = action1;
                cnt += 1;
                int hashID = action0 * pNode->actionAgent[1].actionNum + action1;
                auto it = pNode->nxt.find(hashID);
                double winValue = 0;
                if (it == pNode->nxt.end()) {
                    TankGame::TankField nxtfield = pNode->Field;
                    nxtfield.nextAction[0][0] = pNode->actionAgent[0].validMove[action0][0];
                    nxtfield.nextAction[0][1] = pNode->actionAgent[0].validMove[action0][1];
                    nxtfield.nextAction[1][0] = pNode->actionAgent[1].validMove[action1][0];
                    nxtfield.nextAction[1][1] = pNode->actionAgent[1].validMove[action1][1];
                    
                    // debug << pNode->actionAgent[0].validMove[action0] << ' ' << pNode->actionAgent[1].validMove[action1] << endl;

                    if (nxtfield.DoAction() == 0)
                        throw std::runtime_error("(stimulate)the best is invalid");
                    Pool.emplace_back(new MCTnode(&nxtfield, s, t));
                    pNode->nxt[hashID] = Pool.back();
                    winValue = VirtualGame(&nxtfield).run(&fast, maxTurns);
                    ++ Pool.back() -> visitCount;
                    Pool.back()->winCount += winValue;
                    result = winValue;
                    break;
                }
                else pNode = it->second;
            }
            // if (verbose) debug << endl; 
            for (int i=0; i<cnt; ++i)
                backPropagation(pNodeStk[i], action0Stk[i], action1Stk[i], result);
        }
        void backPropagation(MCTnode *pNode, int action0, int action1, double winValue) {
            int side = pNode->Field.mySide;
            ++pNode -> visitCount;
            pNode->winCount += winValue;
            ++pNode ->actionAgent[0].visitSum[action0];
            pNode->actionAgent[0].winSum[action0] += side == 0?winValue:1-winValue;
            ++pNode ->actionAgent[1].visitSum[action1];
            pNode ->actionAgent[1].winSum[action1] += side==1?winValue:1-winValue; 
        }
        std::vector<MCTnode *> Pool;
};

void debugPrint(std::vector<std::pair<Action,std::pair<double,double> > > actions)
{
    for (auto x:actions)
        debug << x.first << ": " << x.second.first << "/" << x.second.second <<
            " : " << x.second.first/x.second.second << endl;
}
Action chooseAction(std::vector<std::pair<Action,std::pair<double,double> > > actions)
{

}

int main()
{
    // cout << 1 << endl;
    freopen("in.txt", "r", stdin);
    freopen("out.txt", "w", stdout);
    srand((unsigned)time(nullptr));

    string data, globaldata;
    TankGame::ReadInput(cin, data, globaldata);
    MCTSAgent *Agent = new MCTSAgent(0.05, 81, 81, 5, 1);
    // Action action = Agent->getAction(TankGame::field);
    std::vector<std::pair<Action, std::pair<double,double> > > actions = Agent->getActions(TankGame::field);
    debugPrint(actions);
    Action action = chooseAction(actions);
    TankGame::SubmitAndExit(action[0], action[1]);
    // TankGame::field->DebugPrint();
    // Greedy GreedyBot(TankGame::field);
    // std::pair<TankGame::Action, TankGame::Action> ret = GreedyBot.getAction(5);
    // TankGame::SubmitAndExit(ret.first, ret.second);
    // TankGame::SubmitAndExit(RandAction(0), RandAction(1));
}



/* 

Todo:
    - evaluate the situation after every action during the course MCTS stimulate by randomly moving.
    - specially mark some situations and complete the evaluation
    - according to dataset, update the action probability.
*/