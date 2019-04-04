package softtest.depchain.c;

import java.io.UnsupportedEncodingException;

public class numberToChinese {
	   public static String toOct(String s)
	    {
	        String result = "";
	        byte[] bytes = s.getBytes();
	        for (byte b : bytes)
	        {
	            int b1 = b;
	            if (b1 < 0) b1 = 256 + b1;
	            result += "\\" + (b1 / 64) % 8 +  "" + (b1 / 8) % 8 + "" + b1 % 8;
	        }
	        return result;
	    }

	    public static String getOct(String s) throws UnsupportedEncodingException
	    {
	        String[] as = s.split("\\\\");
	        byte[] arr = new byte[as.length - 1];
	        for (int i = 1; i < as.length; i++)
	        {
	            int sum = 0;
	            int base = 64;
	            for (char c : as[i].toCharArray())
	            {
	                sum += base * ((int)c - '0');
	                base /= 8;
	            }
	            if (sum >= 128) sum = sum - 256;
	            arr[i - 1] = (byte)sum;
	        }
	        return new String(arr,"utf-8"); //����������룬������뷽ʽ������޸��£��������Կ�unicode gbk�ȵ�
	    }
	    
	    
	    public static int getEnd(String str) {
	    	int ans = -1;
	    	int start = str.split("\\\\")[0].length();
	    	for(int i = start ; i < str.length() ; i ++) {
	    		if(str.charAt(i) == '\\') {
	    			continue;
	    		}
	    		if(str.charAt(i) > '9' || str.charAt(i) < '0') {
	    			while(str.charAt(i) > '9' || str.charAt(i) < '0') {
	    				i --;
	    			}
	    			return i;
	    		}
	    	}
	    	return ans;
	    }
	    
	    /**
	     *�ж�ǰ�����ַ�Ϊ����
	     * @param str
	     * @return
	     * 
	     */
	    public static int getNumChinese(String str) {
	    	str = str.trim();
	    	int ans = 0;
	    	for(int i = 0 ; i < str.length() ; i ++) {
	    		if(isChineseChar(str.charAt(i))) {
	    			ans ++;
	    		}
	    		else {
	    			return ans;
	    		}
	    	}
	    	return ans;
	    }
	    
	    /**
	     * �ж�һ���ַ��Ƿ��Ǻ���
	     * PS�����ĺ��ֵı��뷶Χ��[\u4e00-\u9fa5]
	     *
	     * @param c ��Ҫ�жϵ��ַ�
	     * @return �Ǻ���(true), ���Ǻ���(false)
	     */
	    public static boolean isChineseChar(char c) {
	        return String.valueOf(c).matches("[\u4e00-\u9fa5]");
	    }

	    /**
	     * ���һ���˽��Ƶ��±�
	     * @return
	     * @throws UnsupportedEncodingException 
	     */
	    public static int getLast(String str) throws UnsupportedEncodingException {
	    	String string = getOct(str);
	    	int num = getNumChinese(string);
	    	int end = num * 4 * 3 ;
	    	return end;
	    }
	    
	    public static int getBegin(String str) {
	    	int begin = - 1;
	    	for(int i = 0 ; i < str.length() - 1 ; i ++) {
	    		if(str.charAt(i) == '\\' && str.charAt(i + 1) == '\\') {
	    			return i ;
	    		}
	    	}
	    	return begin;
	    }
	    
	    public static String reverse(String str) throws UnsupportedEncodingException {
	    	str = str.trim();
	    	int begin = getBegin(str);
	    	if(begin == -1) return str;
	    	System.out.println(str + " lsc begin  " + begin);
	    	String str1 = str.substring(0 , begin);
	    	str = str.substring(begin);
	    	int end = getLast(str);
	    	if(end <= 0) return str;
	    	String string = str.substring(0 , end + 1);
	    	string = getOct(string);
	    	return str1 + "\\"+string.trim()+ str.substring(end + 1);
	    }
	    
	    public static void main(String[] args) throws java.io.UnsupportedEncodingException {
	        String s = "C:\\Users\\Triste\\Desktop\\\\346\\265\\213\\350\\257\\225\\spell\\getopt.h";
//	        s = "C:\\Users\\Triste\\Desktopspell\\getopt.h";
	        System.err.println(s);
	        System.err.println(reverse(s));
	        
	        String o = toOct(s);
	        System.out.println(o);
	        
	        o =  "\\\\346\\265\\213\\350\\257\\225\\123\\spell\\counter.c";
	        
	     
	        int end = getLast(o);
	        System.out.println("end : "+end);
	        o = o.substring(0 , end + 1);
	        System.out.println(o);

	        
	        
	        s = getOct(o);
	        System.out.println(getNumChinese(s));
	        System.out.println(s.length());
	        System.out.println(s);
	    }
}

//o = "\\346\\265\\213\\350\\257\\225";
