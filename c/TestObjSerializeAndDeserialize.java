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
 *<p>Description�� ���Զ�������л��ͷ�����<p>
 *@author lsc
 *@createTime 2018-10-16 ����16:16 
 */

public class TestObjSerializeAndDeserialize {
	static String[] strings = new String[6];
	public static void main(String[] args) throws Exception {
		strings = args; 
		SerializeDepChainTest();          //���л�DepChainTest����
		DepChainTest p = DeserializeDepChainTest();       //�����л�DepChainTest����
		
		System.out.println(p.analyse2());

		//���д����������û�ܵõ�����
		System.out.println(p.getCondLineMap());//�����������ڵ�
		System.out.println("����·����");
		for(String s : p.pathSet) {//����·��
			System.out.println(s);
		}
	

		p.listSCVP(args[2]);                    //��ӡ��Ӧ������scvp��Ϣ
		
		
		
//		System.out.println(MessageFormat.format("name={0}, age={1},sex={2},money={3}" ,p.getName(),p.getAge(),p.getSex(),p.getMoney()));
	}
	
	/**
	 * MethodeName:SerializeDepChainTest
	 * Description:���л�DepChainTest����
	 * @author lsc
	 * @throws FileNotFoundException
	 * @throws IOException
	 */
	private static void SerializeDepChainTest() throws FileNotFoundException,IOException {
		DepChainTest DepChainTest = new DepChainTest(strings);
	
		//ObjectOutputStream �������������DepChainTest����洢��E�̵�DepChainTest.txt�ļ��У����DepChainTest��������л�����
		ObjectOutputStream oo = new ObjectOutputStream(new FileOutputStream(new File("E:/DepChainTest.txt")));
		oo.writeObject(DepChainTest);
		System.out.println("DepChainTest�������л��ɹ�");
		oo.close();
	}
	
	/**
	 * MethodName: DeserializeDepChainTest
	 * Description: �����л�DepChainTest����
	 * @author lsc
	 * @return
	 * @throws Exception
	 * @throws IOException
	 */
	private static DepChainTest DeserializeDepChainTest() throws Exception,IOException {
		ObjectInputStream ois = new ObjectInputStream(new FileInputStream("E:/DepChainTest.txt"));
		DepChainTest DepChainTest = (DepChainTest) ois.readObject();
		System.out.println("DepChainTest�������л��ɹ�");
		return DepChainTest;
	}
	
	
	
	
}
