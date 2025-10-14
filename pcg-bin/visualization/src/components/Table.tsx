import React from "react";

export default function Table({
  columns,
  data,
}: {
  columns: string[];
  data: string[][];
}) {
  const [isVisible, setIsVisible] = React.useState(true);

  const toggleVisibility = () => {
    setIsVisible(!isVisible);
  };

  return (
    <div style={{ position: "relative", width: "300px" }}>
      <button
        onClick={toggleVisibility}
        style={{
          position: "absolute",
          top: "0",
          right: "0",
          zIndex: "1",
          padding: "5px 10px",
          backgroundColor: "#f2f2f2",
          border: "1px solid black",
          cursor: "pointer",
        }}
      >
        {isVisible ? "-" : "+"}
      </button>
      <table
        style={{
          borderCollapse: "collapse",
          width: "300px",
          backgroundColor: "white",
          boxShadow: "0 0 10px rgba(0,0,0,0.1)",
          marginBottom: "20px",
        }}
      >
        <thead>
          <tr>
            {columns.map((column, index) => (
              <th
                key={index}
                style={{
                  border: "1px solid black",
                  padding: "8px",
                  backgroundColor: "#f2f2f2",
                }}
              >
                {column}
              </th>
            ))}
          </tr>
        </thead>
        <tbody>
          {isVisible && data.map((row, rowIdx) => (
            <tr key={rowIdx}>
              {row.map((value, colIdx) => (
                <td
                  key={colIdx}
                  style={{ border: "1px solid black", padding: "8px" }}
                >
                  <code>
                    <div dangerouslySetInnerHTML={{ __html: value }} />
                  </code>
                </td>
              ))}
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}
