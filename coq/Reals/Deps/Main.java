import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

public class Main {
	public static void main(String[] args) throws FileNotFoundException, IOException {
		String path = "..\\deps.txt";

		System.out.println(".PHONY: ALL");
		System.out.println();

		StringBuilder output = new StringBuilder();
		Set<String> vos = new HashSet<>();

		try (BufferedReader br = new BufferedReader(new FileReader(new File(path)))) {
			String line;
			while ((line = br.readLine()) != null) {
				String[] parts = line.split(":");
				String[] partsL = parts[0].trim().split(" ");
				String[] partsR = parts[1].trim().split(" ");
				String base = partsL[0].trim();
				if (base.endsWith(".vo")) {
					vos.add(base);

					StringBuilder volist = new StringBuilder(" ");
					for (int i = 0; i < partsR.length; ++i) {
						String dep = partsR[i].trim();
						if (dep.endsWith(".vo")) {
							vos.add(dep);
							volist.append(" " + dep);
						}
					}

					String b = base.replace(".vo", "");

					output.append(b + ".vo : " + b + ".v" + volist).append("\n");
					output.append("\t C:\\Coq\\bin\\coqc " + b + ".v").append("\n");
					output.append("\n");
				}
			}
		}

		StringBuilder allvos = new StringBuilder();
		vos.forEach(s -> allvos.append(" ").append(s));

		System.out.println("ALL:"+allvos);
		System.out.println();

		System.out.print(output.toString());
	}
}
