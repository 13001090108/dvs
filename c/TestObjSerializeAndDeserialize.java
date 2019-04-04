package softtest.depchain.c;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.io.SerializablePermission;
import java.text.MessageFormat;
import java.util.HashMap;

import com.alibaba.fastjson.JSON;
import com.alibaba.fastjson.JSONObject;
import com.sun.xml.internal.ws.encoding.soap.DeserializationException;

import softtest.cfg.c.Graph;
import softtest.cfg.c.GraphVisitor;


/**
 *<p>ClassNam: TestObjSerializeAndDeserialize
 *<p>Description： 测试对象的序列化和反序列<p>
 *@author lsc
 *@createTime 2018-10-16 下午16:16 
 */

public class TestObjSerializeAndDeserialize {
	static String[] strings = new String[6];
	public static void main(String[] args) throws Exception {
		strings = args; 
		SerializeDepChainTest();          //序列化DepChainTest对象
		DepChainTest p = DeserializeDepChainTest();       //反序列化DepChainTest对象
		
		System.out.println(p.analyse2());

		//这行代码在输出中没能得到体现
		System.out.println(p.getCondLineMap());//高亮的条件节点
		System.out.println("调用路径：");
		for(String s : p.pathSet) {//调用路径
			System.out.println(s);
		}
	

		p.listSCVP(args[2]);                    //打印响应函数的scvp信息
		
		
		
//		System.out.println(MessageFormat.format("name={0}, age={1},sex={2},money={3}" ,p.getName(),p.getAge(),p.getSex(),p.getMoney()));
	}
	
	/**
	 * MethodeName:SerializeDepChainTest
	 * Description:序列化DepChainTest对象
	 * @author lsc
	 * @throws FileNotFoundException
	 * @throws IOException
	 */
	private static void SerializeDepChainTest() throws FileNotFoundException,IOException {
		DepChainTest DepChainTest = new DepChainTest(strings);
	
		//ObjectOutputStream 对象输出流，将DepChainTest对象存储到E盘的DepChainTest.txt文件中，完成DepChainTest对象的序列化操作
		ObjectOutputStream oo = new ObjectOutputStream(new FileOutputStream(new File("E:/DepChainTest.txt")));
		oo.writeObject(DepChainTest);
		System.out.println("DepChainTest对象序列化成功");
		oo.close();
	}
	
	/**
	 * MethodName: DeserializeDepChainTest
	 * Description: 反序列化DepChainTest对象
	 * @author lsc
	 * @return
	 * @throws Exception
	 * @throws IOException
	 */
	private static DepChainTest DeserializeDepChainTest() throws Exception,IOException {
		ObjectInputStream ois = new ObjectInputStream(new FileInputStream("E:/DepChainTest.txt"));
		DepChainTest DepChainTest = (DepChainTest) ois.readObject();
		System.out.println("DepChainTest对象反序列化成功");
		return DepChainTest;
	}
	
	
	
	
}
