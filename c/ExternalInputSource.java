package softtest.depchain.c;

public class ExternalInputSource {
	private String fileName;
	private String varName;
	private String funcName;
	private int line;
	
	public String getFileName() {
		return fileName;
	}
	public void setFileName(String fileName) {
		this.fileName = fileName;
	}
	public String getVarName() {
		return varName;
	}
	public void setVarName(String varName) {
		this.varName = varName;
	}
	public int getLine() {
		return line;
	}
	public void setLine(int line) {
		this.line = line;
	}
	public String getFuncName() {
		return funcName;
	}
	public void setFuncName(String funcName) {
		this.funcName = funcName;
	}

	public ExternalInputSource() {
	}
	@Override
	public String toString() {
		return "["+ fileName + "_" + funcName + "_" + varName+ "_" + line + "]";
	}
	
	
	
}